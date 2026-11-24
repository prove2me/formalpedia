-- Prove2me | Theorems.Thm_GoodViews_mutualInfo_chain_rule
-- name    : GoodViews.mutualInfo_chain_rule
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:39:25.519493+00:00
-- url     : https://prove2.me/theorems/9bc56c00-4eff-4c19-9012-b41ddd825c4d
-- title:
--   Appendix A.1, Property (2): chain rule for mutual information
-- statement:
--   Let $A,B,C$ be finitely-valued random variables on a finite probability space. Then
--
--   $$I(A;B,C)=I(A;B)+I(A;C\mid B),$$
--
--   where $(B,C)$ is the joint random variable.
--
--   This is property (2), the chain rule, of the paper's recap of mutual information (Appendix A.1), used in the proofs of Propositions A.1-A.3.
-- source:
--   Tian, Sun, Poole, Krishnan, Schmid and Isola, What Makes for Good Views for Contrastive Learning?, arXiv:2005.10243v3 (2020), Appendix A.1, Properties of MI, item (2) (Chain Rule), p. 15

import Mathlib
import Definitions.Def_GoodViews_Basic

open Finset

namespace GoodViews

theorem mutualInfo_chain_rule {S α β γ : Type} [Fintype S] [Fintype α] [Fintype β]
    [Fintype γ] (P : S → ℝ) (hP : IsPMF P) (A : S → α) (B : S → β) (C : S → γ) :
    mutualInfo P A (fun ω => (B ω, C ω)) = mutualInfo P A B + condMutualInfo P A C B := by sorry

end GoodViews
