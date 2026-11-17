-- Prove2me | Theorems.Thm_MFHeisGibbs_Supplement_theorem_4
-- name    : MFHeisGibbs.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:17:58.139537+00:00
-- url     : https://prove2.me/theorems/47dfa9db-e163-44d5-8020-04568d325aef
-- title:
--   Theorem 4 (Linear gap transfer) — $\gamma(\mathcal L_{F,\sigma},V)\ge\kappa\,c_{\mathrm{eff}}(\omega_{\mathrm{trn}})$ from uniform coherent bounds, with the bounds (126) on $c_{\mathrm{eff}}$
-- statement:
--   Let $H$ be an arbitrary Hamiltonian on $\mathcal H_n$, $0<\beta<\infty$, $\sigma>0$, and let $\{K^{(a)}\}_{a\in A}$ be a finite family of self-adjoint jumps with $K^{(a)}_\nu=0$ for all $\nu>\Lambda/\beta$ and all $a$, for some $\Lambda\ge0$. Let $\mathcal L_{F,\sigma}$ be the OFT Lindbladian of these jumps with the Metropolis filter $f_M$ and width $\sigma$, and for a KMS filter $h$ let $\mathcal L^h_C$ be the coherent Lindbladian of the same jumps with filter $h$; both keep the coherent correction. Let $h_{\omega,\pm}$, $w$ and $c_{\mathrm{eff}}$ be as in (122), (123), (125), and let $\Phi$ be the standard normal distribution function. Then:
--
--   1. every $h_{\omega,\pm}$ ($\omega\in\mathbb R$, both signs) is a KMS filter: it is continuous and $h(x)=e^{-x/2}\overline{h(-x)}$;
--   2. $w$ is even, and $w(\omega)=e^{-\sigma^2/8}e^{-\beta|\omega|/2}$;
--   3. let $V$ be a subspace of operators invariant under $\mathcal L_{F,\sigma}$ that contains $I$ or is KMS-orthogonal to $I$, and contains an observable of positive variance, and let $\omega_{\mathrm{trn}}\in(0,\infty]$. If for some $\kappa>0$
--
--   $$\mathcal E^h_C(O)\ge\kappa\min_{x\in[-\Lambda,0]}|h(x)|^2\operatorname{Var}(O)\quad\text{for all }O\in V\text{ and all }h\in\{h_{\omega,\pm}:|\omega|\le\omega_{\mathrm{trn}}\},$$
--
--   then
--
--   $$\gamma(\mathcal L_{F,\sigma},V)\ge\kappa\,c_{\mathrm{eff}}(\omega_{\mathrm{trn}});$$
--
--   4. $c_{\mathrm{eff}}(\infty)\ge1-\Phi\big(\max\{\sigma/2,\Lambda/(2\sigma)\}\big)$;
--   5. for finite $\omega_{\mathrm{trn}}>0$,
--
--   $$c_{\mathrm{eff}}(\omega_{\mathrm{trn}})\ge\frac{\omega_{\mathrm{trn}}\beta}{\sigma\sqrt{2\pi}}\exp\Big(-\frac{(\max\{\Lambda,\beta\omega_{\mathrm{trn}}\}+\sigma^2/2)^2}{2\sigma^2}\Big).$$
--
--   The theorem turns any spectral-gap lower bound for coherent Lindbladians that is uniform over the Gaussian filters $h_{\omega,\pm}$ into a gap lower bound for the Metropolis OFT Lindbladian, with every constant explicit; the paper applies it to the mean-field Heisenberg model in Corollary 6.
--
--   **Formalization Note** All Gibbs quantities ($\rho$, $\langle\cdot,\cdot\rangle_\rho$, $\mathcal E$, $\operatorname{Var}$, $\gamma$) are those of the Gibbs state of $H$ at the same $\beta$. "KMS filter" means continuity and the KMS relation without the normalization of (4), as Appendix B says. The bandwidth hypothesis is one-sided, as printed.
--
--   Differences from the source:
--   - encoding: ω_trn ∈ (0, ∞] → an extended nonnegative real ωt with 0 < ωt, region {ω | ofReal |ω| ≤ ωt}; the second bound of (126) for ω_trn < ∞ is stated for every real ωt > 0 at ofReal ωt; reason: same values, ∞ included
--   - encoding: the sign ± → a Boolean pm (true for +); reason: Lean convention; both signs are quantified
--   - encoding: the OFT integral (10) with K̂(ω) of (11) → its Bohr expansion Σ_{ν,μ} κ(ν,μ) K_ν† X K_μ; reason: the integrand expands to this finite sum of scalar integrals, so the map is the same
--   - encoding: a family {K^(a)}_{a∈A} → a finite index type A; reason: L^h_C and L_{F,σ} are sums over a (p.50), and Proposition 5 speaks of finite families
--   - encoding: the Dirichlet form E_L(O) = ⟨O, −L[O]⟩_ρ (24) → its real part Re⟨O, −L[O]⟩_ρ; reason: L^h_C (Lemma 21) and L_{F,σ} are KMS detailed balanced, so the form is real and the values coincide
--   - encoding: min_{x∈[−Λ,0]} |h(x)|² → sInf of the image of [−Λ, 0]; reason: Λ ≥ 0 and h_{ω,±} is continuous, so the infimum over the compact interval is attained and equals the minimum
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), Theorem 4, (122)–(126), p.53 (PDF 54); setting of Appendix B.1, p.50 (PDF 51)

import Definitions.Def_MFHeisGibbs_Supplement_GibbsH
import Definitions.Def_MFHeisGibbs_Supplement_Transfer

open Matrix
open scoped ENNReal

namespace MFHeisGibbs

namespace Supplement

/-- **Theorem 4 (Linear gap transfer)**, (122)–(126), Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818
(version dated November 3, 2026, sha256 164d57ba…), p.53 (PDF 54), in the setting of Appendix B.1, p.50
(`0 < β < ∞`, `σ > 0`, `H` an arbitrary Hamiltonian on `H_n`).

Let `{K^(a)}_{a ∈ A}` be self-adjoint jumps with `K^(a)_ν = 0` for all `ν > Λ/β`, `Λ ≥ 0`. Then
(a) every `h_{ω,±}` is a KMS filter; (b) `w` is even; (c) `w(ω) = e^{−σ²/8} e^{−β|ω|/2}`; (d) for every
subspace `V` invariant under the Metropolis OFT Lindbladian `L_{F,σ}`, containing `I` or KMS-orthogonal
to `I`, with an observable of positive variance, every `ω_trn ∈ (0, ∞]` and `κ > 0` with (124),
`γ(L_{F,σ}, V) ≥ κ c_eff(ω_trn)`; (e), (f) the lower bounds (126) on `c_eff`.

**Formalization Note.** Both Lindbladians keep the coherent correction of (116). "KMS filter" for `h` is
`KMSRel` (continuity and the KMS relation, no normalization), as on p.50. The sign `±` is `pm : Bool`.
The Gibbs quantities are those of `H` at
the same `β`: the KMS inner product is the published `SysBathGibbs.kmsInner β H`. The second bound of (126) is stated for finite `ω_trn > 0` as `c_eff(ENNReal.ofReal ω_trn)`. The family
of jumps is finite (`Fintype A`), as `L^h_C = ∑_a` requires. -/
theorem theorem_4 {n : ℕ} (H : Op n) (hH : H.IsHermitian) (β : ℝ) (hβ : 0 < β) (s : ℝ) (hs : 0 < s)
    {A : Type} [Fintype A] (K : A → Op n) (hK : ∀ a, (K a).IsHermitian) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hband : ∀ a, ∀ ν : ℝ, Λ / β < ν → bohrComp hH (K a) ν = 0) :
    (∀ (ω : ℝ) (pm : Bool), KMSRel (hOm β s ω pm)) ∧
    (∀ ω : ℝ, wM β s (-ω) = wM β s ω) ∧
    (∀ ω : ℝ, wM β s ω = Real.exp (-s ^ 2 / 8) * Real.exp (-(β * |ω|) / 2)) ∧
    (∀ (V : Submodule ℂ (Op n)) (ωt : ℝ≥0∞) (κ : ℝ),
      (∀ X ∈ V, LFfam hH β s fM K X ∈ V) →
      ((1 : Op n) ∈ V ∨ ∀ X ∈ V, SysBathGibbs.kmsInner β H 1 X = 0) →
      (∃ O ∈ V, 0 < gibbsVarH H β O) →
      0 < ωt → 0 < κ →
      (∀ O ∈ V, ∀ ω : ℝ, ENNReal.ofReal |ω| ≤ ωt → ∀ pm : Bool,
        κ * minSqOn Λ (hOm β s ω pm) * gibbsVarH H β O ≤
          dirichletH H β (LCh hH β (hOm β s ω pm) K) O) →
      κ * ceff β s Λ ωt ≤ sectorGapH H β (LFfam hH β s fM K) (V : Set (Op n))) ∧
    1 - normalCdf (max (s / 2) (Λ / (2 * s))) ≤ ceff β s Λ ⊤ ∧
    (∀ ωt : ℝ, 0 < ωt →
      ωt * β / (s * Real.sqrt (2 * Real.pi)) *
          Real.exp (-(max Λ (β * ωt) + s ^ 2 / 2) ^ 2 / (2 * s ^ 2)) ≤
        ceff β s Λ (ENNReal.ofReal ωt)) := by sorry

end Supplement

end MFHeisGibbs
