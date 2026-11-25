-- Prove2me | Theorems.Thm_GoodViews_mutualInfo_nonneg
-- name    : GoodViews.mutualInfo_nonneg
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T05:38:49.731465+00:00
-- url     : https://prove2.me/theorems/e91ab817-1343-470c-b5bc-7d34a91f5edd
-- title:
--   Appendix A.1, Property (1): nonnegativity of mutual information
-- statement:
--   Let $A,B,C$ be finitely-valued random variables on a finite probability space. Then
--
--   $$I(A;B)\ge0,\qquad I(A;B\mid C)\ge0.$$
--
--   This is property (1) of the paper's recap of mutual information (Appendix A.1, citing Cover and Thomas), used throughout the proofs of Propositions A.1-A.3.
-- source:
--   Tian, Sun, Poole, Krishnan, Schmid and Isola, What Makes for Good Views for Contrastive Learning?, arXiv:2005.10243v3 (2020), Appendix A.1, Properties of MI, item (1), p. 15

import Mathlib
import Definitions.Def_GoodViews_Basic

open Finset

namespace GoodViews

theorem mutualInfo_nonneg {S α β γ : Type} [Fintype S] [Fintype α] [Fintype β] [Fintype γ]
    (P : S → ℝ) (hP : IsPMF P) (A : S → α) (B : S → β) (C : S → γ) :
    0 ≤ mutualInfo P A B ∧ 0 ≤ condMutualInfo P A B C := by sorry

end GoodViews
