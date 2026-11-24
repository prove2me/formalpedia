-- Prove2me | Theorems.Thm_IdentifiableVAE_permutation_identifiability_k_eq_one
-- name    : IdentifiableVAE.permutation_identifiability_k_eq_one
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:00:34.536421+00:00
-- url     : https://prove2.me/theorems/6b912298-79bf-4e05-9c3c-7e92ee2ad3c1
-- title:
--   Theorem 3 (with the regularity its proof uses): identifiability up to $\sim_P$ for $k=1$
-- statement:
--   Assume the hypotheses of Theorem 1 (as stated above) with $k=1$, and write $T_i=T_{i,1}$. Assume further:
--
--   1. each $T_i$ is continuous and its turning points are isolated: every $t$ has a punctured neighbourhood on each side of which $T_i$ is strictly monotonic;
--   2. (3.i) no $T_i$ is monotonic, meaning that none is strictly increasing or strictly decreasing;
--   3. (3.ii) all partial derivatives of $f$ exist and are continuous; moreover $f$ is a $C^1$ embedding (a homeomorphism onto its image) whose differential is injective at every point.
--
--   Let $\tilde\theta$ be a parameter describing a model on $U$ with the same properties: $\tilde T$ satisfies (iii), each $\tilde T_i$ is continuous with isolated turning points and is not monotonic, and $\tilde f$ is a $C^1$ embedding with injective differential. Let $\tilde f$ also have the same image $\mathcal X=f(\mathbb{R}^n)$ as $f$. If $p_{\tilde\theta}(x\mid u)=p_\theta(x\mid u)$ for all $u\in U$, then there are an invertible matrix $A$ with exactly one nonzero entry in each row and column, that is a scaled permutation matrix, and $c\in\mathbb{R}^n$. For almost every $z$, $f(z)=\tilde f(\tilde z)$ for some $\tilde z$, and
--
--   $$T_i(z_i)=A_{i,\sigma(i)}\tilde T_{\sigma(i)}(\tilde z_{\sigma(i)})+c_i\quad(1\le i\le n).$$
--
--   **Formalization Note** The statement adds the hypotheses that the printed proof uses but the printed theorem does not state.
--   1. Continuity of $T_i$ and $\tilde T_i$. Without it the statement is false. For example, take the Gaussian location model of Proposition 1 and redefine $T_i(t)=t$ at the two points $t=0,1$ so that $T_i$ is not monotonic. The observed laws are unchanged, and the rotation of Proposition 1 gives a competing parameter that is not related by a permutation.
--   2. The proof says that "by hypothesis" $v=f^{-1}\circ\tilde f$ is $C^1$ with nonvanishing Jacobian. Continuous partial derivatives of $f$ and $\tilde f$ do not give this. For example, $\tilde f=f\circ(z_1^3,z_2)$ gives a $v$ that is not differentiable. An injective $C^1$ map need not even have a continuous inverse. The embedding conditions, together with a common image $\mathcal X$ (the paper's standing notation), make $v$ a $C^1$ diffeomorphism of $\mathbb{R}^n$.
--   3. The proof chooses a neighbourhood in which $T_i$ has a single minimum, which needs isolated turning points.
--
--   The printed proof also assumes "without loss of generality" that every $\tilde T_a$ attains a minimum at the chosen point. This fails when some of the maps have only maxima. A topological argument at a point where every non-constant $\tilde T_a$ has a strict local extremum repairs it. That argument compares the level set of $T_i\circ v_i$, a $C^1$ hypersurface, with that of $\sum_a A_{i,a}\tilde T_a(z_a)$. The conclusion is stated almost everywhere.
-- source:
--   Khemakhem, Kingma, Monti and Hyvärinen, Variational Autoencoders and Nonlinear ICA: A Unifying Framework, AISTATS 2020, arXiv:1907.04809v4, Section 4.2, Theorem 3, p. 6; proof in Appendix B.4, eqs. (45)-(47), pp. 16-17

import Mathlib
import Definitions.Def_IdentifiableVAE_Basic

open MeasureTheory

namespace IdentifiableVAE

theorem permutation_identifiability_k_eq_one {n d m : ℕ} (hnd : n ≤ d)
    (U : Set (Fin m → ℝ)) (hU : IsOpen U)
    (Pε : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Pε] (hPε : Pε ≪ volume)
    (θ : Param n d m 1) (hθ : IsParam θ U)
    (h1 : CharFunZeroNull Pε) (h3 : SuffStatRegular θ) (h4 : HasInvertibleL θ U)
    (hTc : ∀ i, Continuous (θ.T i 0)) (hTi : ∀ i, IsolatedTurningPoints (θ.T i 0))
    (h31 : NotMonotoneStats θ) (h32 : HasContinuousPartials θ.f) (hemb : IsC1Embedding θ.f) :
    IdentifiableUpTo Pε U
      {θ' | IsParam θ' U ∧ SuffStatRegular θ' ∧ (∀ i, Continuous (θ'.T i 0)) ∧
        (∀ i, IsolatedTurningPoints (θ'.T i 0)) ∧ NotMonotoneStats θ' ∧
        HasContinuousPartials θ'.f ∧ IsC1Embedding θ'.f ∧ Set.range θ'.f = Set.range θ.f}
      SimPAE θ := by sorry

end IdentifiableVAE
