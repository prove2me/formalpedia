-- Prove2me | Theorems.Thm_NishtAbel2024V5_theorem_15
-- name    : NishtAbel2024V5.theorem_15
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T04:17:46.22105+00:00
-- url     : https://prove2.me/theorems/f4053932-f55c-468b-b34d-263104461ce2
-- title:
--   Theorem 15 (V5): Soundness of Type-Based Termination Checking (Algorithm 2 Implies Well-Typedness and Strong Normalization)
-- statement:
--   The main end-to-end soundness theorem of Nisht and Abel (2024) (Chapter 6, Section 6.5, Theorem 15, p. 59), uniting algorithmic size inference, constraint solving, size-change termination checking, and the ordinal reducibility semantics of System $F_\omega^{\mathsf{cop,SCT}}$.\n\nLet $W$ be a closed run-time world of function declarations with distinct names containing $\Sigma \cup \Xi_{\mathsf{annot}}$, where every global signature declaration $g \in \Sigma$ is well-kinded (`SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star`) and semantically valid in $W$ (`SemValid W sig`). If Algorithm 2 accepts the unsized mutual block $\Xi$ and produces the size-annotated block $\Xi_{\mathsf{annot}}$ (`Algorithm2Accepts sig Ξ Ξannot`), then:\n$$\mathsf{Algorithm2Accepts}(\Sigma, \Xi, \Xi_{\mathsf{annot}}) \;\wedge\; W \models \Sigma \implies (\Sigma \vdash \Xi_{\mathsf{annot}}) \;\wedge\; (W \models \Xi_{\mathsf{annot}}).$$\n\nIn particular, $\Xi_{\mathsf{annot}}$ is both syntactically well-typed in System $F_\omega^{\mathsf{cop,SCT}}$ (`BlockTy sig Ξannot`) and semantically valid / strongly normalizing in $W$ (`SemValid W Ξannot`).
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Chapter 6, Section 6.5, p. 59, Theorem 15

import Definitions.Def_NishtAbel2024V5_Syntax
import Definitions.Def_NishtAbel2024V5_Semantics
import Definitions.Def_NishtAbel2024V5_Inference

namespace NishtAbel2024V5

theorem theorem_15 (W sig Ξ Ξannot : List FunDecl)
    (hsigwf : ∀ g ∈ sig, SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star)
    (hacc : Algorithm2Accepts sig Ξ Ξannot)
    (hW : ∀ d ∈ sig ++ Ξannot, d ∈ W)
    (hnames : (W.map FunDecl.name).Nodup)
    (hclosed : ∀ d ∈ W, (Tm.lam d.clauses).Closed)
    (hsig : SemValid W sig) :
    BlockTy sig Ξannot ∧ SemValid W Ξannot := by sorry

end NishtAbel2024V5
