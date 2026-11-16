-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_Supplement_theorem_10
-- name    : LeakageSpectral.Shannon.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:44:38.454086+00:00
-- url     : https://prove2.me/theorems/d19a146d-8c39-4739-a689-fa8d7171d18c
-- title:
--   Theorem 10, p. 18 — primitive–quotient composition and Möbius decomposition
-- statement:
--   Let $\mathbb G=\mathbb Z_m$ be a cyclic group with the discrete $\sigma$-algebra and $\tau$ a leakage channel (a Markov kernel from $\mathbb Z_m$ to a measurable space) with $I(S;L)>0$; let $Q(\gamma)$ be the order-$\gamma$ primitive spectral mass of Theorem 8. For a character $\chi_w$ of $\mathbb Z_m$, the **quotient variable** is $Y^{(w)}=S+\ker\chi_w\in\mathbb Z_m/\ker\chi_w$, and the **normalized quotient leakage** is $R=I_{\chi^2}(Y^{(w)};L)/I_{\chi^2}(S;L)$. Then:
--
--   1. for every character $\chi_w$ of order $\gamma=\operatorname{ord}\chi_w$,
--   $$\frac{I_{\chi^2}(Y^{(w)};L)}{I_{\chi^2}(S;L)}=\sum_{g\mid\gamma}Q(g),$$
--   so the normalized quotient leakage depends only on $\gamma$; call it $R(\gamma)$;
--   2. for every $\gamma\mid m$,
--   $$Q(\gamma)=\sum_{g\mid\gamma}\mu\!\left(\frac{\gamma}{g}\right)R(g),$$
--   with $\mu$ the Möbius function.
--
--   The primitive spectrum can therefore be recovered from the leakage about the natural quotient variables.
--
--   Differences from the source:
--
--   - encoding: a cyclic group ℤ_m (§5.1) → ZMod m with m ≠ 0 (NeZero m), discrete σ-algebra; reason: the same group
--   - encoding: Y^{(w)} = S + ker χ_w and I_χ²(Y^{(w)}; L) → quotientJoint τ w, the push-forward of the law of (S, L) under (s, l) ↦ (s + ker χ_w, l), and the base chiSquareMI of it on the finite quotient with the quotient σ-algebra; reason: the law of (Y^{(w)}, L); the quotient σ-algebra of a discrete space is discrete
--   - reading: R(γ) defined through a character χ_w with γ = ord χ_w → clause 1 for every character w (the trivial one gives 0 = Q(1) = 0); clause 2 for every R : ℕ → ℝ with R (orderOf w) = normalized quotient leakage of w for all w; reason: clause 1 shows R is well defined as a function of the order; every γ ∣ m is the order of some character, so the hypothesis of clause 2 is satisfiable
--   - encoding: Möbius function μ_M → ArithmeticFunction.moebius, cast to ℝ; reason: the same function
--   - reading: a channel without share index ("we may omit the subscript i, assuming that the leakages are i.i.d.", §2.1, p. 5) → one Markov kernel τ used for every share: globalJoint (fun _ => τ) d; reason: the paper's standing i.i.d. convention for unindexed statements
--   - encoding: standing assumption I(S;L) > 0 of §2.1, p. 5, not repeated in the theorem → hypothesis 0 < shannonMI (localJoint τ); reason: the standing assumption of the section, written as a binder as in the base mission
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Theorem 10, p. 18

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
import Definitions.Def_LeakageSpectral_Shannon_Supplement_Defs
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeakageSpectral.Shannon.Supplement

/-- Ueno, STOC 2027 submission #326, Theorem 10, p. 18: primitive–quotient composition and
decomposition, for a cyclic group `G = ℤ_m` and one channel `τ` with `I(S; L) > 0`. For a character
`χ_w` of order `γ`, the normalized quotient leakage `I_χ²(S + ker χ_w; L) / I_χ²(S; L)` equals
`R(γ) = ∑_{g ∣ γ} Q(g)` (so it depends only on `γ`), and `Q(γ) = ∑_{g ∣ γ} μ(γ/g) R(g)` for every
`γ ∣ m`, `μ` the Möbius function. -/
theorem theorem_10 (m : ℕ) [NeZero m] {L : Type*} [MeasurableSpace L] (τ : Kernel (ZMod m) L)
    [IsMarkovKernel τ] (hdep : 0 < shannonMI (localJoint τ)) :
    (∀ w : AddChar (ZMod m) ℂ,
      quotientLeakage τ w = ∑ g ∈ (orderOf w).divisors, primitiveMass τ g) ∧
    ∀ R : ℕ → ℝ, (∀ w : AddChar (ZMod m) ℂ, R (orderOf w) = quotientLeakage τ w) →
      ∀ γ ∈ m.divisors,
        primitiveMass τ γ = ∑ g ∈ γ.divisors, (ArithmeticFunction.moebius (γ / g) : ℝ) * R g := by sorry

end LeakageSpectral.Shannon.Supplement
