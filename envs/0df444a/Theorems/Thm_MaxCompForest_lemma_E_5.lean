-- Prove2me | Theorems.Thm_MaxCompForest_lemma_E_5
-- name    : MaxCompForest.lemma_E_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:46.117591+00:00
-- url     : https://prove2.me/theorems/425a5c2f-b682-4c8a-ac32-5f6f4d897930
-- title:
--   Lemma E.5 — physical-recursion terminal interface
-- statement:
--   Let $G$ be a connected simple graph with positive conductances, $1\le q<|V(G)|$, $1\le k\le|V(G)|-1$, and $0<\varepsilon\le1$ rational. Choose rational $0<\alpha\le1$, put $\xi=\varepsilon/(16k)$, $\rho=\alpha/k^2$, and an integer $M_0>k+k/(\xi\rho)$. Run the physical recursion of Lemma E.2, where an all-low quotient $H$ with at most $q$ vertices enumerates its residual forests exactly. Suppose that at every other all-low quotient $H$, with residual budget $j$, there are a positive semidefinite vertex response $R_H$, a rational vertex factor $\mathbf F$ and $0<\omega\le\varepsilon/(512k)$ such that, for every family $F$ of at most $k$ labels,
--   $$
--   (1-\omega)P_F\preceq K^{(H)}_F\preceq(1+\omega)P_F,\qquad(1-\omega)P_F\preceq\widehat P_F\preceq(1+\omega)P_F,
--   $$
--   with $P_F=C_F^{1/2}B_F^{\top}(D^{-1}+R_H)B_FC_F^{1/2}$ and $\widehat P_F=C_F^{1/2}B_F^{\top}(D^{-1}+\mathbf F^{\top}\mathbf F)B_FC_F^{1/2}$. Suppose also that a terminal method returns a $j$-forest $\widehat F$ of $H$ with
--   $$
--   \det\widehat P_{\widehat F}\ge\frac{\max_{|F|=j}\det\widehat P_F}{1+\varepsilon/8}.
--   $$
--   Then exact original-graph scoring of all complete candidates returns $k$ distinct original labels forming a forest $F_{\mathrm{best}}$ with
--   $$
--   P_{T\sim\mathrm{WST}(G)}(F_{\mathrm{best}}\subseteq T)\ge\frac{1}{1+\varepsilon}\max_{|J|=k}P_{T\sim\mathrm{WST}(G)}(J\subseteq T).
--   $$
--   The recursion has depth at most $k$ and fanout below $M_0$, and small-quotient enumeration uses at most $\binom q2(k+1)^2$ surviving labels.
--
--   This lemma reduces the goal to supplying the response, the factor and the optimizer at the larger all-low quotients.
--
--   Differences from the source:
--   - reading: “one can supply … Suppose also that a terminal method returns” → a function `term` giving the forest at each node, with the response, factor and tolerance existentially supplied at each all-low node; reason: the lemma is an interface; these are its hypotheses, node by node
--   - reading: “All include steps are exact, and each complete candidate incurs only one terminal approximation loss” → no separate clause; it is carried by the $(1+\varepsilon)$ conclusion here and by (E.3) in `lemma_E_2`; reason: a description of the proof, with no further quantitative content
--   - encoding: “exact original-graph scoring … returns” → the conclusion holds for every maximizer of `inclProb` among the candidates; reason: exact scoring returns such a maximizer
--   - generalization: positive rational conductances → positive real conductances; reason: the argument uses only positivity; rationality matters only for the machine statements, and rational inputs are a special case
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma E.5, p.40

import Mathlib
import Definitions.Def_MaxCompForest_physTerminals
import Definitions.Def_MaxCompForest_physAllLow
import Definitions.Def_MaxCompForest_inclProb
import Definitions.Def_MaxCompForest_K
import Definitions.Def_MaxCompForest_onLabels
import Definitions.Def_MaxCompForest_respForm
import Definitions.Def_MaxCompForest_deg
import Definitions.Def_MaxCompForest_featGram
import Definitions.Def_MaxCompForest_ratFeat
import Definitions.Def_MaxCompForest_IsForest
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

/-- **Lemma E.5 (Physical-recursion terminal interface).** `term S` is the terminal method's forest at the all-low
node `S`; the response, factor and tolerance are supplied at each such node with more than `q` vertices (the
recursion here has the small-quotient exit, `physNode … q`). The conclusion is about every maximizer of the exact
original score among all complete candidates.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.40. -/
theorem lemma_E_5 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [LinearOrder E]
    (G : WGraph V E) (hG : G.IsConnected) (hsimple : G.IsSimple) (q k : ℕ) (hq1 : 1 ≤ q)
    (hqn : q < Fintype.card V) (hk : 1 ≤ k) (hkn : k + 1 ≤ Fintype.card V) (ε α : ℚ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hα0 : 0 < α) (hα1 : α ≤ 1) (M0 : ℕ)
    (hM0 : (k : ℚ) + k / ((ε / (16 * k)) * (α / (k : ℚ) ^ 2)) < M0)
    (term : ∀ S : Finset E, Finset (ContractE G S))
    (hterm : ∀ S ∈ physAllLow G k α M0 q,
      ∃ (R : Matrix (ContractV G S) (ContractV G S) ℝ) (r : ℕ)
        (Ft : Fin r → ContractV G S → ℚ) (ω : ℝ),
        R.PosSemidef ∧ 0 < ω ∧ ω ≤ (ε : ℝ) / (512 * k) ∧
        (∀ F : Finset (ContractE G S), F.card ≤ k →
          let H := contract G S
          let P := respForm H (deg H) R F
          let Phat := respForm H (deg H) (featGram (ratFeat Ft)) F
          (onLabels (K H) F - (1 - ω) • P).PosSemidef ∧
          ((1 + ω) • P - onLabels (K H) F).PosSemidef ∧
          (Phat - (1 - ω) • P).PosSemidef ∧ ((1 + ω) • P - Phat).PosSemidef) ∧
        (term S).card = k - S.card ∧ IsForest (contract G S) (term S) ∧
        (∀ F : Finset (ContractE G S), F.card = k - S.card →
          (respForm (contract G S) (deg (contract G S)) (featGram (ratFeat Ft)) F).det ≤
            (1 + (ε : ℝ) / 8) *
              (respForm (contract G S) (deg (contract G S)) (featGram (ratFeat Ft)) (term S)).det)) :
    let cands : Finset (Finset E) := physTerminals G k α M0 q ∪
      (physAllLow G k α M0 q).attach.image fun S => S.1 ∪ liftLabels G S.1 (term S.1)
    (∀ d S, S ∈ physNodes G k α M0 q d → S.card = d ∧ d ≤ k) ∧
    (∀ d S, S ∈ physNodes G k α M0 q d → ∀ L, physNode G k α M0 q S = .branch L → L.card < M0) ∧
    (∀ d S, S ∈ physNodes G k α M0 q d → Fintype.card (ContractV G S) ≤ q →
      Fintype.card (ContractE G S) ≤ q.choose 2 * (k + 1) ^ 2) ∧
    cands.Nonempty ∧ (∀ F ∈ cands, F.card = k) ∧
    ∀ Fbest ∈ cands, (∀ F ∈ cands, inclProb G F ≤ inclProb G Fbest) →
      IsForest G Fbest ∧
        ∀ J : Finset E, J.card = k → inclProb G J ≤ (1 + (ε : ℝ)) * inclProb G Fbest := by sorry

end MaxCompForest
