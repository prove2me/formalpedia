-- Prove2me | Theorems.Thm_OnlineLearningOCO_Agnostic_lemma_3_7
-- name    : OnlineLearningOCO.Agnostic.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:59.926533+00:00
-- url     : https://prove2.me/theorems/c698f582-0901-44c8-a340-a5cca1a67a0d
-- title:
--   Lemma 3.7 — every h ∈ H is reproduced by some Expert(i₁,…,i_L) with L ≤ Ldim(H)
-- statement:
--   Let $H \subseteq \{0,1\}^X$ be a hypothesis class with Littlestone dimension $\operatorname{Ldim}(H) < \infty$, let $x_1,\dots,x_T$ be any sequence of instances, and let $h \in H$. Then there exist $L \le \operatorname{Ldim}(H)$ and indices $1 \le i_1 < \dots < i_L \le T$ such that, when Expert$(i_1,\dots,i_L)$ runs on $x_1,\dots,x_T$,
--
--   $$
--   \hat y_t = h(x_t) \qquad \text{for every round } t = 1,\dots,T.
--   $$
--
--   The lemma says that the finite family of experts indexed by at most $\operatorname{Ldim}(H)$ rounds covers the behaviour of the whole (possibly infinite) class $H$ on any instance sequence. It is the key step reducing agnostic online learning of $H$ to prediction with expert advice.
--
--   **Formalization Note** The index set is $I = \{i_1-1,\dots,i_L-1\} \subseteq \{0,\dots,T-1\}$ (0-based) with $|I| \le \operatorname{Ldim}(H)$. Since the expert never reads labels, the statement holds for every labelling $y$ of the instances that may appear in the history; the set $I$ is chosen before the labels. The expert breaks ties toward $0$, as in its box on p. 166.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 167, Lemma 3.7

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_OnlineLearningOCO_Agnostic_expertAlg

namespace OnlineLearningOCO.Agnostic

open UnderstandingML

/-- Lemma 3.7, p. 167. Let `H` be a hypothesis class with `Ldim(H) < ∞`, `x₁,…,x_T` a sequence of
instances and `h ∈ H`. There is a set `I ⊆ {0,…,T−1}` of (0-based) rounds with `|I| ≤ Ldim(H)`
such that Expert(I) predicts `h(x_t)` on every round `t`. The expert ignores labels, so this holds
whatever labels `y` accompany the instances in the history. -/
theorem lemma_3_7 {X : Type*} (H : Set (X → Bool)) (hH : ldim H < ⊤) {T : ℕ} (x : Fin T → X)
    (h : X → Bool) (hh : h ∈ H) :
    ∃ I : Finset ℕ, I ⊆ Finset.range T ∧ (I.card : ℕ∞) ≤ ldim H ∧
      ∀ (y : Fin T → Bool) (t : Fin T),
        expertAlg H I (history (fun s ↦ (x s, y s)) t) (x t) = h (x t) := by sorry

end OnlineLearningOCO.Agnostic
