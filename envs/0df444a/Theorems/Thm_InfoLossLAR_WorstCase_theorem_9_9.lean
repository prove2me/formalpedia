-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_theorem_9_9
-- name    : InfoLossLAR.WorstCase.theorem_9_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:06:47.30092+00:00
-- url     : https://prove2.me/theorems/f7a21b46-6a2a-427f-af55-ffcb6c475464
-- title:
--   Theorem 9.9 — the fixed family admits fixed-order Gaussian T-AFTs with accuracy $C_RqL^{-(R+1)/4}+\mathrm{negl}_R(L)+\epsilon_{\mathrm{num}}$
-- statement:
--   Consider the family of §9.9: $L=\lambda+2$, $N=\lambda$, $\sigma=L$, $q$ the least prime $\ge2^{16}L^{64}$, $d=qL^{96}+2L^{128}$, and $T$, $P=\mathbf 1^\top$ of Definition 6.3. For every calibration order $R$ there are a constant $C_R>0$ and a nonnegative negligible function $\mathrm{negl}_R$, both depending only on $R$, such that for every integer $c\ge1$ with $R\ge4c+267$ and every numerical budget $\epsilon_{\mathrm{num}}=\frac14L^{-(e+2)}$ with an integer $e\ge c$ (so $\epsilon_{\mathrm{num}}\le\frac14L^{-(c+2)}$), there is a uniform PPT sampler $\mathrm{Sample}_c(1^\lambda,\mathrm{pp})\to(Q,\beta)\in\mathbb Z^{d\times d}\times\mathbb Z^d$ whose every execution returns $Q\bmod q\in\mathrm{GL}_d(\mathbb F_q)$, such that for all sufficiently large $\lambda$, with $e\leftarrow D_{\mathbb Z^d,\sigma}$ independent,
--   $$\Delta\big(\mathcal L(Qe+\beta\bmod q),U(\mathcal F_{T,0})\big)\le C_R\,q\,L^{-(R+1)/4}+\mathrm{negl}_R(L)+\epsilon_{\mathrm{num}},$$
--   and which satisfies Definition 5.3: the same distance is at most $\lambda^{-c}$ for all sufficiently large $\lambda$.
--
--   Differences from the source:
--   - reading: "for the fixed calibration order $R$ chosen above" ($R\ge4c+267$, §9.10) and the constants $C_R$, $\mathrm{negl}_R$ → for every $R$, constants depending only on $R$, valid for every $c\ge1$ with $R\ge4c+267$; reason: the subscript $R$ and Proposition 9.6 fix them by $R$ alone
--   - reading: "$\epsilon_{\mathrm{num}}\le\frac14L^{-(c+2)}$" (§9.10) → every budget $\frac14L^{-(e+2)}$ with integer $e\ge c$; reason: §9.10 chooses one budget below ¼L^{−(c+2)} without pinning it; e = c is the printed bound ¼L^{−(c+2)} itself, and every smaller inverse power of L is covered as well, so the statement contains the source's choice
--   - reading: "uniform PPT sampler" → `IsPPTAffineSampler`: one classical polynomial-time map from (coins, code of $(1^\lambda,\mathrm{pp})$) to the code of $(Q,\beta)$, with polynomially many coins; reason: the paper names no model; reading only $1^\lambda$, pp and coins is the source independence
--   - encoding: $e\leftarrow D_{\mathbb Z^d,\sigma}$ and $Qe+\beta\bmod q$ → $e\leftarrow\chi_G=D_{\mathbb Z^d,\sigma}\bmod q$ and $Qe+\beta$ over $\mathbb F_q$; reason: the same law, as $Q,\beta$ are integral
--   - encoding: the label in $\mathbb F_q$ → a vector of $\mathbb F_q^1$; reason: $\ell=1$
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 58 §§9.9–9.10, p. 59, Theorem 9.9

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_Family

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-- Theorem 9.9 (Constructive fixed-order Gaussian AFT), p. 59, for the fixed family of §9.9
(`L = λ + 2`, `N = λ`, `σ = L`, `q` the least prime `≥ 2^{16} L^{64}`,
`d = qL^{96} + 2L^{128}`, `T` and `P = 1ᵀ` of Definition 6.3). For every calibration order `R`
there are a constant `C_R > 0` and a nonnegative negligible function `negl_R` such that for every
integer `c ≥ 1` with `R ≥ 4c + 267` (§9.10) and every numerical budget
`ε_num = (1/4) L^{−(e+2)}` with an integer `e ≥ c` (so `ε_num ≤ (1/4) L^{−(c+2)}`, §9.10) there is
a uniform classical PPT sampler
`Sample_c(1^λ, pp) → (Q, β) ∈ ℤ^{d×d} × ℤ^d` whose every output has `Q mod q ∈ GL_d(𝔽_q)`, such
that for all sufficiently large `λ`, with `x ← D_{ℤ^d,σ}` independent,
`Δ(L(Qx + β mod q), U(F_{T,0})) ≤ C_R q L^{−(R+1)/4} + negl_R(L) + ε_num`,
and which satisfies Definition 5.3: this distance is at most `λ^{−c}` for all large `λ`. -/
theorem theorem_9_9 (R : ℕ) :
    ∃ C_R : ℝ, 0 < C_R ∧ ∃ negl_R : ℕ → ℝ, Negligible negl_R ∧
      ∀ c : ℕ, 1 ≤ c → 4 * c + 267 ≤ R → ∀ e : ℕ, c ≤ e →
        ∃ (m : Polynomial ℕ)
          (S : (lam : ℕ) → (Fin (m.eval lam) → Bool) →
            Matrix (Fin (famd lam)) (Fin (famd lam)) ℤ × (Fin (famd lam) → ℤ)),
          IsPPTAffineSampler famInput famd m S ∧
          (∀ (lam : ℕ) (ρ : Fin (m.eval lam) → Bool), IsUnit (matModq (famq lam) (S lam ρ).1).det) ∧
          (∃ lam₀ : ℕ, ∀ lam ≥ lam₀,
            sdist (transportLaw (S lam) (chiG (famq lam) (famd lam) (famσ lam)))
                (unifZeroFiber (famLabel lam)) ≤
              C_R * (famq lam : ℝ) * (famL lam : ℝ) ^ (-((R : ℝ) + 1) / 4) +
                negl_R (famL lam) + (1 / 4) * (famL lam : ℝ) ^ (-((e : ℝ) + 2))) ∧
          (∃ lam₀ : ℕ, ∀ lam ≥ lam₀,
            sdist (transportLaw (S lam) (chiG (famq lam) (famd lam) (famσ lam)))
                (unifZeroFiber (famLabel lam)) ≤ (lam : ℝ) ^ (-(c : ℝ))) := by sorry

end InfoLossLAR.WorstCase
