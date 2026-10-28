-- Prove2me | Theorems.Thm_Intersectionality_Generic_beta_one_identity
-- name    : Intersectionality.Generic.beta_one_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:17.071049+00:00
-- url     : https://prove2.me/theorems/41903823-f507-44bd-9ec1-5a870d44ec6e
-- title:
--   Proof of Theorem 1(a) — a representative nonintersectional policy forces x* = β_𝟎, q_{e_i}(β_{e_i}) = β_𝟎 and β_𝟏 = (q⁻¹_{e_n}∘⋯∘q⁻¹_{e_1})(β_𝟎)
-- statement:
--   Let $X \subset \mathbb{R}$ be a nonempty interval, $n \in \mathbb{N}$, $\alpha \in (0,1)$, and let $Q$ be a rich and commutative family of increasing bijections of $X$. Let $p \in P$ with $p(g) > 0$ for all $g$, and write $\beta_g = F_g^{-1}(1-\alpha)$. Suppose $q$ is a nonintersectional policy with all $q_g \in Q$, and that $(q, x^*)$ yields a representative outcome at capacity $\alpha$. Then three identities hold:
--   1. $x^* = \beta_{\mathbf 0}$;
--   2. $q_{e_i}(\beta_{e_i}) = \beta_{\mathbf 0}$ for every $i = 1, \dots, n$;
--   3. the quantile of the group $\mathbf 1$ is
--
--   $$\beta_{\mathbf 1} = \big(q_{e_n}^{-1} \circ \cdots \circ q_{e_1}^{-1}\big)(\beta_{\mathbf 0}).$$
--
--   The third identity is a nongeneric coincidence between quantiles, and it is the fact that Lemma 2 turns into the impossibility of part (a).
--
--   **Formalization Note.** Identity 3 is stated as a left fold over $i = 1, \dots, n$ that applies $q_{e_1}^{-1}$ first, matching the printed order. The basis vectors are indexed from $0$ in Lean. The inverse is `Function.invFun`, which is the true inverse because each $q_{e_i}$ is a bijection.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 10 (PDF 11), proof of Theorem 1, part (a), "Let 0 and 1 be the vector of zeros and ones"

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting

namespace Intersectionality.Generic

theorem beta_one_identity (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (n : ℕ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X)) (hQ : IsPolicyFamily Q)
    (p : DistSpace X n) (hpos : ∀ g, 0 < groupMass p.1 g)
    (q : Grp n → (↥X → ↥X)) (hqQ : ∀ g, q g ∈ Q) (hq : IsNonintersectional q) (xs : ↥X)
    (hrep : IsRepresentative p.1 α q xs) :
    xs = quantile p.1 α (zeroGrp n) ∧
    (∀ i : Fin n, q (unitGrp i) (quantile p.1 α (unitGrp i)) = quantile p.1 α (zeroGrp n)) ∧
    quantile p.1 α (oneGrp n) =
      (List.finRange n).foldl (fun x i => Function.invFun (q (unitGrp i)) x)
        (quantile p.1 α (zeroGrp n)) := by sorry

end Intersectionality.Generic
