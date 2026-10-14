-- Prove2me | Theorems.Thm_InfoRelaxTS_Gap_lemma_3
-- name    : InfoRelaxTS.Gap.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:17.222043+00:00
-- url     : https://prove2.me/theorems/e357166c-20bf-43da-84e1-d23a6daa7e63
-- title:
--   Lemma 3, pp. 63–64 — instantaneous suboptimality of the first action for z^TS, z^IRS.FH and z^IRS.V-Zero
-- statement:
--   Fix a horizon $T\ge1$, numbers $\mu_a$ ($a\in\mathcal A$) and an array $\hat\mu_{a,n}$ ($a\in\mathcal A$, $n\ge0$). For a payoff rule on action sequences $a_{1:T}\in\mathcal A^T$, let $Q_1(a)$ be the largest total payoff of a sequence with $a_1=a$, and let $a_1^*$ be any maximizer of $Q_1$. Consider the three payoff rules of the penalties $z^{\rm TS}$, $z^{\rm IRS.FH}$ and $z^{\rm IRS.V\text{-}Zero}$: at time $t$ the action $a_t$ earns $\mu_{a_t}$, $\hat\mu_{a_t,T-1}$, or $\hat\mu_{a_t,n_{t-1}(a_t)}$ respectively, where $n_{t-1}(a)$ is the number of pulls of $a$ before time $t$. Then for every arm $a$:
--
--   1. for $z^{\rm TS}$, $$Q_1(a_1^*)-Q_1(a)=\mu_{a_1^*}-\mu_a;$$
--   2. for $z^{\rm IRS.FH}$, $$Q_1(a_1^*)-Q_1(a)=\hat\mu_{a_1^*,T-1}-\hat\mu_{a,T-1};$$
--   3. for $z^{\rm IRS.V\text{-}Zero}$, if $Q_1(a)<Q_1(a_1^*)$, then $$Q_1(a_1^*)-Q_1(a)\le\max_{0\le n\le T-1}\hat\mu_{a_1^*,n}-\hat\mu_{a,0}.$$
--
--   The lemma expresses the loss of a first action in terms of mean-reward metrics; it is the time-1 case of the per-step bounds that drive the proof of Theorem 3.
--
--   **Formalization Note** The statement is deterministic: the true outcome only supplies the numbers $\mu_a$ and $\hat\mu_{a,n}$, so they are arbitrary reals here. The page fixes $T$ without a bound; $T\ge1$ is needed for a first action. Part 3 carries the hypothesis $Q_1(a)<Q_1(a_1^*)$: as printed, (190) is false when $a$ is itself an optimal first action (for $K=T=2$, $\hat\mu_{1,0}=\hat\mu_{1,1}=0.5$, $\hat\mu_{2,0}=1$, $\hat\mu_{2,1}=0.4$, both arms are optimal first actions and (190) would claim $0\le-0.5$). The hypothesis is the proof's own remark that "the suboptimality is incurred only when $n^*_a=0$". $Q_1(a)$ is the maximum over all sequences starting with $a$ of the unrolled sum (181)–(182).
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, pp. 63–64, Lemma 3, (188)–(190)

import Mathlib
import Definitions.Def_InfoRelaxTS_Gap_Setting

namespace InfoRelaxTS.Gap

theorem lemma_3 {K : ℕ} (T : ℕ) (hT : 1 ≤ T) (μv : Fin K → ℝ) (m : Fin K → ℕ → ℝ) :
    (∀ aStar : Fin K, (∀ a', Q1 (payTS (T := T) μv) a' ≤ Q1 (payTS (T := T) μv) aStar) →
      ∀ a, Q1 (payTS (T := T) μv) aStar - Q1 (payTS (T := T) μv) a = μv aStar - μv a) ∧
    (∀ aStar : Fin K, (∀ a', Q1 (payFH (T := T) m) a' ≤ Q1 (payFH (T := T) m) aStar) →
      ∀ a, Q1 (payFH (T := T) m) aStar - Q1 (payFH (T := T) m) a = m aStar (T - 1) - m a (T - 1)) ∧
    (∀ aStar : Fin K, (∀ a', Q1 (payVZ (T := T) m) a' ≤ Q1 (payVZ (T := T) m) aStar) →
      ∀ a, Q1 (payVZ (T := T) m) a < Q1 (payVZ (T := T) m) aStar →
        Q1 (payVZ (T := T) m) aStar - Q1 (payVZ (T := T) m) a ≤
          (Finset.range T).sup' (Finset.nonempty_range_iff.mpr (by omega)) (fun n => m aStar n)
            - m a 0) := by sorry

end InfoRelaxTS.Gap
