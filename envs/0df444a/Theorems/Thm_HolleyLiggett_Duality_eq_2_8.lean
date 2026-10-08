-- Prove2me | Theorems.Thm_HolleyLiggett_Duality_eq_2_8
-- name    : HolleyLiggett.Duality.eq_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:40:43.322353+00:00
-- url     : https://prove2.me/theorems/8666fe65-55ee-483a-9330-0470936ed75e
-- title:
--   (2.8), p. 647 — last-step decomposition of the proximity process: P_η(η_{n+1} ∈ B(F)) = Σ P_η(η_n ∈ B(⋃ N_{i,k_i})) ∏ f_i(k_i)
-- statement:
--   Let $\eta_n$ be the discrete-time proximity process determined by $\{N_{i,k}\}$ (with $N_{i,0}=\emptyset$) and $\{f_i\}$ on a countable site set $I$. For every $n\ge0$, every configuration $\eta\in S$ and every finite $F\subset I$,
--   $$P_\eta(\eta_{n+1}\in B(F))=\sum_{(k_i)_{i\in F}}P_\eta\Big(\eta_n\in B\Big(\bigcup_{i\in F}N_{i,k_i}\Big)\Big)\,\prod_{i\in F}f_i(k_i),$$
--   the sum over all sequences $(k_i)_{i\in F}$ of nonnegative integers.
--
--   This conditions on the last step of the proximity process; it is the proximity half of the induction step in the proof of Theorem (1.6). Comparing it with (2.5) and applying the induction hypothesis proves (1.7) at time $n+1$.
--
--   **Formalization Note.** $P_\eta(\eta_n\in\cdot)$ is the $n$-step law of the chain with transition function (1.1), defined by iterating `Measure.bind`; the identity relies on the measurability of $\eta\mapsto Q(\eta,\cdot)$, which holds and is not assumed.
-- source:
--   Holley and Liggett, Ergodic theorems for weakly interacting infinite systems and the voter model, Ann. Probab. 3 (1975), p. 647, (2.6)–(2.8)

import Mathlib
import Definitions.Def_HolleyLiggett_Duality_Setting

namespace HolleyLiggett.Duality

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- (2.8): `P_η(η_{n+1} ∈ B(F)) = Σ P_η(η_n ∈ B(⋃_{i∈F} N_{i,k_i})) P(X_{i,1} = k_i ∀ i ∈ F)`,
the sum over all sequences `(k_i)_{i∈F}`. -/
theorem eq_2_8 {I : Type*} [Countable I] [DecidableEq I] (N : I → ℕ → Finset I)
    (hN0 : ∀ i, N i 0 = ∅) (f : I → PMF ℕ)
    (n : ℕ) (η : Config I) (F : Finset I) :
    proxLaw N f η (n + 1) (zeroOn F) =
      ∑' k : (↥F → ℕ),
        proxLaw N f η n (zeroOn (Finset.univ.biUnion (fun i : ↥F => N i (k i)))) *
          ∏ i : ↥F, f i (k i) := by sorry

end HolleyLiggett.Duality
