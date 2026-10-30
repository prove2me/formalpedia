-- Prove2me | Theorems.Thm_JuschenkoMonod_tfae_almostInvariant_lampInvariantMean_invariantMean_half_invariantMean_one
-- name    : JuschenkoMonod.tfae_almostInvariant_lampInvariantMean_invariantMean_half_invariantMean_one
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:25:32.726813+00:00
-- url     : https://prove2.me/theorems/f3c1ba43-9a19-49ca-b47f-862e4e31fec0
-- title:
--   Lemma 3.1 — almost invariant vectors concentrated on {ω_{x₀} = 0}, invariant means for 𝒫_f(X) ⋊ G, and G-invariant means of weight 1/2 or 1 on the sets containing x₀ are equivalent
-- statement:
--   Let a group $G$ act transitively on a set $X$, and let $x_0 \in X$. Give $\{0,1\}^X$ the symmetric Bernoulli measure, and let $g \in G$ act on functions on $\{0,1\}^X$ by $(gf)(\omega) = f(g^{-1}\omega)$, where $(g^{-1}\omega)_x = \omega_{gx}$. The following are equivalent:
--   1. for every finite $S \subseteq G$ and every $\varepsilon > 0$ there is a complex-valued $f \in L^2(\{0,1\}^X)$ with $\|f\| > 0$, $\|gf - f\| \le \varepsilon\|f\|$ for every $g \in S$, and $\|f|_{\omega_{x_0}=0}\| \ge (1 - \varepsilon)\|f\|$, where $f|_{\omega_{x_0}=0}$ is $f$ multiplied by the indicator function of $\{\omega : \omega_{x_0} = 0\}$;
--   2. there is a mean on $\mathscr P_{\rm f}(X)$ invariant under the affine action of $\mathscr P_{\rm f}(X) \rtimes G$, in which $(F, g)$ sends $E$ to $F \mathbin{\triangle} gE$;
--   3. there is a $G$-invariant mean on $\mathscr P_{\rm f}(X)$ giving weight $1/2$ to the collection of sets containing $x_0$;
--   4. there is a $G$-invariant mean on $\mathscr P_{\rm f}(X)$ giving weight $1$ to the collection of sets containing $x_0$.
--
--   A mean on a set is a finitely additive probability measure defined on all of its subsets.
--
--   *Formalization note.* Condition (i) of the paper asks for a net $\{f_n\}$ of $G$-almost invariant vectors with $\|f_n|_{\omega_{x_0}=0}\|/\|f_n\| \to 1$. It is stated in the equivalent finite form above: such a net yields, for each finite $S$ and $\varepsilon > 0$, one vector satisfying the inequalities, and the vectors chosen for each pair $(S, \varepsilon)$ form such a net. Vectors are not normalized; the inequalities are relative to $\|f\|$.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 783, Lemma 3.1

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_JuschenkoMonod

open MeasureTheory
open scoped ENNReal Pointwise

namespace JuschenkoMonod

theorem tfae_almostInvariant_lampInvariantMean_invariantMean_half_invariantMean_one
    (G X : Type*) [Group G] [MulAction G X] [MulAction.IsPretransitive G X] [DecidableEq X]
    (x₀ : X) :
    List.TFAE
      [∀ S : Finset G, ∀ ε : ℝ, 0 < ε → ∃ f : (X → Fin 2) → ℂ, MemLp f 2 (bernoulli X) ∧
          0 < l2Norm f ∧ (∀ g ∈ S, l2Norm (translate g f - f) ≤ ε * l2Norm f) ∧
          (1 - ε) * l2Norm f ≤ l2Norm (restrictZero x₀ f),
        ∃ m : Set (Finset X) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
          IsLampInvariant G m,
        ∃ m : Set (Finset X) → ℝ≥0∞, IsInvariantMean G m ∧ m {E | x₀ ∈ E} = 1 / 2,
        ∃ m : Set (Finset X) → ℝ≥0∞, IsInvariantMean G m ∧ m {E | x₀ ∈ E} = 1] := by
  sorry

end JuschenkoMonod
