-- Prove2me | Theorems.Thm_HorizontalPadicL_HorizontalMeasure_truncatedFiniteLevel_norm_le_of_primitive_twists_vanish_v2
-- name    : HorizontalPadicL.HorizontalMeasure.truncatedFiniteLevel_norm_le_of_primitive_twists_vanish_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:07:26.308806+00:00
-- url     : https://prove2.me/theorems/be50b64a-1666-417b-91b5-aa377801e379
-- title:
--   Primitive Fourier vanishing contracts truncated marginal coefficients by $1/p$
-- statement:
--   Fix a prime $p$, an integer $m>0$, coordinate exponents $e(n)\ge m$, a subring $R\subseteq\mathbb C_p$, and an $R$-valued horizontal measure $\mu$. Write $q=p^m$ and let $\nu_D$ be its finite-level coefficients after reducing every coordinate modulo $q$.
--
--   Let $A$ be a finite set of coordinates and let $\chi$ be a character of exact order $q$ with support disjoint from $A$. Suppose that $B\ge0$ bounds every coefficient norm of $\nu_{A\cup\operatorname{supp}\chi}$. Assume that all primitive cyclic twists, with arbitrary corrections on $A$, vanish:
--
--   $$\mu(\chi^a\xi)=0\quad\text{whenever }0\le a<q,\ (a,p)=1,\ \operatorname{supp}\xi\subseteq A,\ \operatorname{ord}(\xi)\mid q.$$
--
--   Then every marginal coefficient at level $A$ satisfies
--
--   $$\lVert\nu_A(x)\rVert\le\frac{B}{p}.$$
--
--   This is a finite Fourier estimate: its bound is required at only one finite union of supports. It isolates the local norm contraction needed for finite-correction arguments. There is no integrality, completeness, discrete-valuation, or nonzero-augmentation hypothesis on the coefficient ring or measure.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Section 2.3.3, Proposition 2.10 and its character-orthogonality proof, https://arxiv.org/html/2310.20678v3#S2.SS3.SSS3. This finite marginal-norm estimate is a fibrewise refinement of that argument, not a direct application of Theorem 2.13, which assumes discrete valuation.

import Definitions.Def_KN_TruncatedHorizontalCoefficientsV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- Vanishing of the primitive cyclic Fourier frequencies forces a factor of `p`
in each coefficient of the marginal on the correcting coordinates. -/
theorem HorizontalMeasure.truncatedFiniteLevel_norm_le_of_primitive_twists_vanish_v2
    {p : ℕ} [Fact p.Prime] {e : ℕ → ℕ} {R : Subring ℂ_[p]}
    (μ : HorizontalMeasure R p e) (m : ℕ) (hm : 0 < m) (he : ∀ n, m ≤ e n)
    (A : Finset ℕ) (χ : HorizontalCharacter p e)
    (horder : orderOf χ.toMonoidHom = p ^ m) (hdisjoint : Disjoint χ.support A)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ y : HorizontalFiniteGroup p (fun _ ↦ m) (A ∪ χ.support),
      ‖(μ.truncatedFiniteLevel m he (A ∪ χ.support) y : ℂ_[p])‖ ≤ B)
    (hvanish : ∀ a : ℕ, a < p ^ m → Nat.Coprime a p →
      ∀ ξ : HorizontalCharacter p e, ξ.support ⊆ A →
        orderOf ξ.toMonoidHom ∣ p ^ m →
        μ.eval ((χ.powerOnSupport a).mulOnUnion ξ) = 0) :
    ∀ x : HorizontalFiniteGroup p (fun _ ↦ m) A,
      ‖(μ.truncatedFiniteLevel m he A x : ℂ_[p])‖ ≤ B / (p : ℝ) := by
  sorry

end HorizontalPadicL
