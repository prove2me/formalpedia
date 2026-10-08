-- Prove2me | Theorems.Thm_HolleyLiggett_Duality_theorem_1_6
-- name    : HolleyLiggett.Duality.theorem_1_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:44:28.319261+00:00
-- url     : https://prove2.me/theorems/e2889d6e-4635-4c2b-a47c-98885827db9b
-- title:
--   Theorem (1.6), p. 645 — duality: P_η(η_n ∈ B(F)) = P_F(A_n ∩ C(η) = ∅) for all n ≥ 0, η ∈ S, F ∈ 𝒯
-- statement:
--   Let $I$ be a countable set, and for each $i\in I$ let $N_{i,0}=\emptyset,N_{i,1},\dots$ be finite subsets of $I$ and $f_i$ a probability distribution on the nonnegative integers. Let $\eta_n$ be the discrete-time proximity process on $S=\{0,1\}^I$ with transition function (1.1), and let $A_n$ be the branching process with interference on the finite subsets of $I$ with transition function (1.4), both determined by the same $\{N_{i,k}\}$ and $\{f_i\}$. For $F\in\mathcal T$ let $B(F)=\{\eta:\eta(i)=0\ \forall i\in F\}$ and for $\eta\in S$ let $C(\eta)=\{i:\eta(i)=1\}$. Then for all $n\ge0$, $\eta\in S$ and $F\in\mathcal T$,
--   $$P_\eta(\eta_n\in B(F))=P_F(A_n\cap C(\eta)=\emptyset).\qquad(1.7)$$
--
--   The subscript $\eta$ is the initial state of the proximity process and the subscript $F$ the initial state of the b.p.i. The theorem turns questions about the infinite-dimensional proximity process (for example, whether its law converges to the point mass on the all-zero configuration) into questions about a process of finite sets, which is how Corollaries (3.1) and (4.1) are proved.
--
--   **Formalization Note.** Both sides are built from the fixed transition functions: the left side is the time-$n$ law of the chain with kernel (1.1), obtained by iterating `Measure.bind` from the point mass at $\eta$; the right side is $\sum_B P_F(A_n=B)\,\mathbf 1[B\cap C(\eta)=\emptyset]$ with the $n$-step b.p.i. probabilities from (1.4). The coupling by independent random variables used in the paper's proof is not part of the statement. The page's "$\eta(1)=1$" in (1.2) is read as $\eta(i)=1$.
-- source:
--   Holley and Liggett, Ergodic theorems for weakly interacting infinite systems and the voter model, Ann. Probab. 3 (1975), p. 645, Theorem (1.6), (1.7)

import Mathlib
import Definitions.Def_HolleyLiggett_Duality_Setting

namespace HolleyLiggett.Duality

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Theorem (1.6), (1.7): `P_η(η_n ∈ B(F)) = P_F(A_n ∩ C(η) = ∅)` for all `n ≥ 0`, `η ∈ S`, `F ∈ 𝒯`. -/
theorem theorem_1_6 {I : Type*} [Countable I] [DecidableEq I] (N : I → ℕ → Finset I)
    (hN0 : ∀ i, N i 0 = ∅) (f : I → PMF ℕ)
    (n : ℕ) (η : Config I) (F : Finset I) :
    proxLaw N f η n (zeroOn F) = dualProb N f n F η := by sorry

end HolleyLiggett.Duality
