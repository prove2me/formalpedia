-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_Supplement_lemma_2_5
-- name    : InconsistentDR.Shadow.Supplement.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:13:13.286353+00:00
-- url     : https://prove2.me/theorems/c77f8b84-5cbd-4b19-9a60-eee1ecaaf680
-- title:
--   Lemma 2.5, p. 7 — Fix T(· + v) = −v + Fix(v + T), and S = (0, −v) + {(J_A f, J_{A⁻¹} f) | f ∈ Fix(v + T)}
-- statement:
--   Let $X$ be a real Hilbert space and let $A,B:X\rightrightarrows X$ be maximally monotone operators. Let $J_A=(\mathrm{Id}+A)^{-1}$ and $J_B=(\mathrm{Id}+B)^{-1}$ be their resolvents, let $R_A=2J_A-\mathrm{Id}$, and let
--
--   $$T=\mathrm{Id}-J_A+J_BR_A$$
--
--   be the Douglas–Rachford operator. Write $J_{A^{-1}}=\mathrm{Id}-J_A$. Let $D=\operatorname{dom}A-\operatorname{dom}B$ and $R=\operatorname{ran}A+\operatorname{ran}B$, and let $v=P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$ be the minimal displacement vector. The standing assumption (12) of the paper is in force:
--
--   $$\overline{\operatorname{ran}}(\mathrm{Id}-T)=\overline{D\cap R}=\overline D\cap\overline R .$$
--
--   Let $\mathcal S=\{(z,k)\in X\times X\mid -k\in B(z-v),\ k\in -v+Az\}$ be the extended solution set (18) of the normal problem $0\in -v+Ax+B(x-v)$. Here $T(\cdot+v)$ is the map $y\mapsto T(y+v)$ and $v+T$ is the map $y\mapsto v+Ty$. Then:
--
--   1. (i) $\operatorname{Fix}T(\cdot+v)=-v+\operatorname{Fix}(v+T)$;
--
--   2. (ii) the extended solution set is exactly a translated image of $\operatorname{Fix}(v+T)$:
--
--   $$\mathcal S=(0,-v)+\big\{(J_Ap,\;J_{A^{-1}}p)\;\big|\;p\in\operatorname{Fix}(v+T)\big\}.$$
--
--   Both are equalities of sets and include the case in which the sets are empty. The lemma turns Fejér monotonicity with respect to the shadow pairs of fixed points (Theorem 5.5 (i)) into Fejér monotonicity with respect to $\mathcal S$ (Theorem 5.5 (iv)).
--
--   **Formalization Note** The fixed point that the paper calls $f$ is written $p$. The standing hypotheses of the paper at this point, namely completeness of $X$, maximal monotonicity of $A$ and $B$, the definition of $v$ and assumption (12), are explicit binders, whether or not a proof uses each of them.
--
--   Differences from the source:
--   - encoding: the resolvents are defined by $J_A=(\mathrm{Id}+A)^{-1}$ and $J_B=(\mathrm{Id}+B)^{-1}$ → maps `JA`, `JB` satisfy $x-J_Ax\in A(J_Ax)$ and $x-J_Bx\in B(J_Bx)$ for every $x$; reason: for maximally monotone operators on a Hilbert space these maps exist and are unique (Minty), so they are the resolvents
--   - encoding: $J_{A^{-1}}$ is the resolvent of the operator $A^{-1}$ → `resInv JA` $=\mathrm{Id}-J_A$; reason: the inverse resolvent identity (8) of the paper
--   - encoding: $v$ is the projection of $0$ onto $\overline{\operatorname{ran}}(\mathrm{Id}-T)$ → $v$ is a least-norm point of that closure; reason: the closure is nonempty, closed and convex, so its least-norm point is this projection
--   - encoding: the translated sets $-v+\operatorname{Fix}(v+T)$ and $(0,-v)+\{\cdots\}$ → images of the sets under the two translations; reason: the image of a set under a translation is the translated set
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 7, Lemma 2.5, with (18), p. 7, and the standing assumptions (1)–(2), p. 2, and (12), p. 6

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators

namespace InconsistentDR.Shadow.Supplement

open ThreeOpSplitting.Convergence

/-- Lemma 2.5, p. 7, under (12), for `T = drT JA JB` and the minimal displacement vector `v`:
(i) `Fix T(· + v) = −v + Fix(v + T)`;
(ii) `S = (0, −v) + {(J_A p, J_{A⁻¹} p) | p ∈ Fix(v + T)}` (the paper's `f` is written `p`). -/
theorem lemma_2_5 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT JA JB x)) v)
    (h12 : Standing12 A B JA JB) :
    -- (i)
    (FixSet (fun y => drT JA JB (y + v)) =
      (fun y => -v + y) '' FixSet (fun y => v + drT JA JB y)) ∧
    -- (ii)
    solS A B v =
      (fun c : X × X => ((0 : X), -v) + c) ''
        ((fun p => (JA p, resInv JA p)) '' FixSet (fun y => v + drT JA JB y)) := by sorry

end InconsistentDR.Shadow.Supplement
