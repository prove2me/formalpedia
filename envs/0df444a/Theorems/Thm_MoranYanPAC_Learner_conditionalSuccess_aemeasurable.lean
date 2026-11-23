-- Prove2me | Theorems.Thm_MoranYanPAC_Learner_conditionalSuccess_aemeasurable
-- name    : MoranYanPAC.Learner.conditionalSuccess_aemeasurable
-- status  : Disproved
-- author  : @dbenbenn
-- created : 2026-11-20T15:32:40.746332+00:00
-- url     : https://prove2.me/theorems/63b90627-0b2c-4347-80d3-a4391d32191e
-- title:
--   Theorem 1 well-posedness — the learner's conditional success probability is a.e. measurable
-- statement:
--   **Statement.** Let $X$ be a measurable space, $H$ a nonempty class of functions $X \to \{0,1\}$ with Littlestone dimension $d \ge 1$, and $A_w$ a witness assignment with the SOA clause of Lemma 6 (`MoranYanPAC.Main.SourceWitnesses`). Let $0<\alpha<1$, $0<\varepsilon\le 1$, $0<\delta<1$. Let $P$ be a probability measure on $X \times \{0,1\}$, realizable by one fixed $h^\star \in H$ almost surely, and satisfying the measurable-event convention `VCEventsMeasurable` for the local universe $U$ (loss events of members of $U$, and the one-sample and two-sample uniform-deviation events over $U$). Then for every $n$ the map
--   $$s \mapsto \Pr_{\hat h \sim \mathcal A(s)}\big[L_P(\hat h) \le \alpha\big], \qquad s \in (X \times \{0,1\})^n,$$
--   is almost-everywhere measurable for $P^n$, where $\mathcal A$ = `MoranYanPAC.Learner.littlestoneLearner H d Aw ε δ` is the learner of Section 7.4 (the structural exponential mechanism with $\Delta = 1$, $B = 4(d+1)$ on the candidate set of Algorithm 3).
--
--   **Role.** The goal `MoranYanPAC.Main.private_pac_nearly_linear` of the mission "Nearly Linear Private Learning of Littlestone Classes" asserts, besides privacy and the success bound, that the PAC experiment is well posed (`PACExperimentMeasurable`), and this statement is the only part of that conjunct the paper's argument does not supply. Everything else in the goal is proved from the mission's milestones, with this statement imported: privacy (Theorem 2 with the axioms of Section 7.3), the measurability of the output losses (outputs lie in $U$), and the success bound. The success bound itself needs no measurability of this map, since it is a lower Lebesgue integral bounded below on the measurable event where the uniform deviation bound of Lemma 1 holds and the sample is realizable.
--
--   **What makes it hard.** The candidates are functions on all of $X$, selected through the structural rank and the SOA, which are defined by Littlestone dimensions of restricted classes, i.e. by existential quantification over mistake trees in $X$. The hypotheses make measurable only events defined by realizability of finite labelled patterns over $U$ and uniform-deviation events. No separability is assumed. Whether those hypotheses imply the measurability of $s \mapsto L_P(g)$ for data-selected candidates $g$ is open here; the paper does not discuss measurability.
-- source:
--   Nearly Linear Private Learning of Littlestone Classes, STOC 2027 submission 772, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/772.pdf, p. 3, well-posedness of the PAC experiment in Theorem 1 for the learner of Section 7.4, not addressed in the paper; the conjunct PACExperimentMeasurable of MoranYanPAC.Main.private_pac_nearly_linear

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_PrivLittlestone_localUniverse
import Definitions.Def_MoranYanPAC_Main_Candidates
import Definitions.Def_MoranYanPAC_Main_PACExperiment
import Definitions.Def_MoranYanPAC_Learner

set_option autoImplicit false

open MeasureTheory MoranYanPAC.Main

namespace MoranYanPAC.Learner

theorem conditionalSuccess_aemeasurable {X : Type} [MeasurableSpace X]
    (H : Set (X → Bool)) (d : ℕ) (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw)
    (α ε δ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (P : Measure (X × Bool)) (hP : IsProbabilityMeasure P)
    (hPm : VCEventsMeasurable (PrivLittlestone.localUniverse H d) P) (hR : Realizable H P)
    (n : ℕ) :
    AEMeasurable (fun s : Fin n → X × Bool =>
      conditionalSuccess (littlestoneLearner H d Aw ε δ) P α (List.ofFn s)) (sampleLaw P n) := by
  sorry

end MoranYanPAC.Learner
