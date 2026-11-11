-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_lemma_5_2
-- name    : InfoLossLAR.WorstCase.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:05:21.05285+00:00
-- url     : https://prove2.me/theorems/8de62aa4-e97b-4a64-9e32-152beef71068
-- title:
--   Lemma 5.2 — a T-AFT keeps $QA$ exactly uniform and independent of the transported error
-- statement:
--   Let $q$ be an odd prime, $T$ a rounding matrix with chosen Smith matrices and $\ell\ge1$, and $\chi$ a law on $\mathbb F_q^d$. Let the affine data $(Q,\beta)=\mathrm{samp}(\rho)\in\mathbb Z^{d\times d}\times\mathbb Z^d$ be drawn from a uniform coin $\rho$ in a finite nonempty set $\Omega$, with $Q\bmod q\in\mathrm{GL}_d(\mathbb F_q)$ for every $\rho$, and suppose the transport is $\delta$-accurate ($0\le\delta\le1$): $\Delta(\mathcal L(\mathrm{Eval}(Q,\beta,e)),U(\mathcal F_{T,0}))\le\delta$ for $e\leftarrow\chi$ independent. Sample $A\leftarrow U(\mathbb F_q^{d\times N})$, $e\leftarrow\chi$ and $\rho$ independently, and set $A'=QA$, $e'=\mathrm{Eval}(Q,\beta,e)=Qe+\beta\bmod q$. Then
--   $$\Pr[A'=A_0,\ e'=x_0]=\frac{1}{q^{dN}}\Pr[e'=x_0]\quad\text{for all }A_0,x_0,$$
--   i.e. $A'$ is exactly uniform and independent of $e'$; $\Delta(\mathcal L(e'),U(\mathcal F_{T,0}))\le\delta$; and for $u\leftarrow U(\mathbb F_q^d)$ independent of $(A,\rho)$, $\mathcal L(QA,\mathrm{Eval}(Q,\beta,u))=U(\mathbb F_q^{d\times N})\times U(\mathbb F_q^d)$.
--
--   Differences from the source:
--   - generalization: $\mathrm{AFT}_T=(\mathrm{Sample},\mathrm{Eval})$ a pair of uniform classical PPT algorithms → $(Q,\beta)$ any function of a uniform coin in any finite nonempty set; reason: the lemma uses only invertibility and the accuracy bound; a PPT sampler with $m$ coins is the case $\Omega=\{0,1\}^m$
--   - encoding: "$A'$ exactly uniform and independent of $e'$" → the joint point masses equal $q^{-dN}$ times the law of $e'$; reason: the definition of independence with a uniform marginal
--   - encoding: $\mathrm{Eval}$ → the affine map $Qx+\beta\bmod q$; reason: Definition 5.1's affine-evaluation requirement
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 23, Lemma 5.2

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
import Definitions.Def_InfoLossLAR_WorstCase_Laws

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-- Lemma 5.2 (Basic properties of T-AFT), p. 23. The sampler draws `(Q, β) = samp(ρ)` from a
uniform coin `ρ ∈ Ω`, every output has `Q mod q ∈ GL_d(𝔽_q)`, and `Δ(L(Eval(Q, β, e)),
U(F_{T,0})) ≤ δ` for `e ← χ` independent. With `A ← U(𝔽_q^{d×N})`, `e ← χ` and `ρ` independent,
`A' = QA` and `e' = Eval(Q, β, e)`: (1) the joint law of `(A', e')` is
`U(𝔽_q^{d×N}) ⊗ L(e')` (`A'` exactly uniform and independent of `e'`); (2)
`Δ(L(e'), U(F_{T,0})) ≤ δ`; (3) for `u ← U(𝔽_q^d)` independent of `(A, ρ)`, the law of
`(QA, Eval(Q, β, u))` is `U(𝔽_q^{d×N}) × U(𝔽_q^d)`. -/
theorem lemma_5_2 (q r d N : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (T : Matrix (Fin d) (Fin d) ℤ)
    (S : SmithData q r d T) (hℓ : r < d)
    (χ : (Fin d → ZMod q) → ℝ) (hχ0 : ∀ e, 0 ≤ χ e) (hχ1 : ∑ e, χ e = 1)
    (Ω : Type) [Fintype Ω] [Nonempty Ω]
    (samp : Ω → Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ))
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hinv : ∀ ρ, IsUnit (matModq q (samp ρ).1).det)
    (hfib : sdist (transportLaw samp χ) (unifZeroFiber S.fT) ≤ δ) :
    (∀ (A' : Matrix (Fin d) (Fin N) (ZMod q)) (x' : Fin d → ZMod q),
      (avg fun ρ : Ω => avg fun A : Matrix (Fin d) (Fin N) (ZMod q) =>
        ∑ e : Fin d → ZMod q,
          if matModq q (samp ρ).1 * A = A' ∧ evalAffine (samp ρ).1 (samp ρ).2 e = x'
          then χ e else 0) =
        (Fintype.card (Matrix (Fin d) (Fin N) (ZMod q)) : ℝ)⁻¹ * transportLaw samp χ x') ∧
    sdist (transportLaw samp χ) (unifZeroFiber S.fT) ≤ δ ∧
    (∀ (A' : Matrix (Fin d) (Fin N) (ZMod q)) (x' : Fin d → ZMod q),
      (avg fun ρ : Ω => avg fun A : Matrix (Fin d) (Fin N) (ZMod q) =>
        avg fun u : Fin d → ZMod q =>
          if matModq q (samp ρ).1 * A = A' ∧ evalAffine (samp ρ).1 (samp ρ).2 u = x'
          then (1 : ℝ) else 0) =
        ((Fintype.card (Matrix (Fin d) (Fin N) (ZMod q)) : ℝ) * (q : ℝ) ^ d)⁻¹) := by sorry

end InfoLossLAR.WorstCase
