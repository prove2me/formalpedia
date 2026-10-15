-- Prove2me | Theorems.Thm_OAI_BufferedIsing_jointWeight_logSupermodular
-- name    : OAI.BufferedIsing.jointWeight_logSupermodular
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:13:42.882999+00:00
-- url     : https://prove2.me/theorems/25301156-412d-4123-8f80-98da0431e742
-- title:
--   Log-supermodularity of the pinned two-block Ising marginal
-- statement:
--   Let $G$ be a finite ferromagnetic graph on $V=\{0,\dots,n-1\}$: edge $e$ has endpoints $l(e)\neq r(e)$ and coupling $K_e\ge0$. Let $h\in\mathbb{R}^V$ be an arbitrary external field (of any signs), let $I,J,F\subseteq V$ be arbitrary vertex sets and $\tau\in\{-1,+1\}^V$. Order $\{-1,+1\}^V$ coordinatewise with $-1<+1$, and write $a\wedge a'$ and $a\vee a'$ for the coordinatewise minimum and maximum. Consider the joint weight
--
--   $$W(a,b)=\sum_{\sigma:\ \sigma_I=a_I,\ \sigma_J=b_J,\ \sigma_F=\tau_F}\exp\Bigl(\sum_eK_e\sigma_{l(e)}\sigma_{r(e)}+\sum_vh_v\sigma_v\Bigr).$$
--
--   Then for all configurations $a,a',b,b'\in\{-1,+1\}^V$,
--
--   $$W(a,b)\,W(a',b')\le W(a\wedge a',\,b\wedge b')\;W(a\vee a',\,b\vee b').$$
--
--   So the pinned marginal of the two blocks $(\sigma_I,\sigma_J)$ satisfies the FKG lattice condition. For prescriptions $a\le a'$ and $b\le b'$ it yields $W(a,b')\,W(a',b)\le W(a,b)\,W(a',b')$, the rectangle inequality behind the extreme log-odds bound on ratios of conditional probabilities.
--
--   **Formalization Note** The joint weight is `jointWeight G h I J F τ a b`, and the lattice operations are `⊓` and `⊔` on `Fin n → Bool` with `false < true`, where `false` and `true` stand for $-1$ and $+1$. No disjointness of $I,J,F$ is assumed, so some of the joint weights may vanish.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Marginals.lean#L9-L55

import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals

open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem OAI.BufferedIsing.jointWeight_logSupermodular {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ a a' b b' : Spins n) :
    jointWeight G h I J F τ a b * jointWeight G h I J F τ a' b' ≤
      jointWeight G h I J F τ (a ⊓ a') (b ⊓ b') *
      jointWeight G h I J F τ (a ⊔ a') (b ⊔ b') := by sorry
