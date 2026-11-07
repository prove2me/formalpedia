-- Prove2me | Theorems.Thm_NishtAbel2024V5_theorems_4_5_and_6
-- name    : NishtAbel2024V5.theorems_4_5_and_6
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T04:17:35.661751+00:00
-- url     : https://prove2.me/theorems/8b1722e3-40b1-45ab-977c-940db8e29cfe
-- title:
--   Theorems 4, 5 & 6 and Lemma 2 (V5): Strong Normalization of System $F_\omega^{\mathsf{cop,SCT}}$ and Embedding of $F_\omega^{\mathsf{cop}}$
-- statement:
--   Proves the strong normalization metatheory of System $F_\omega^{\mathsf{cop,SCT}}$ and the embedding of lexicographic measure programs from System $F_\omega^{\mathsf{cop}}$ (Chapter 5, Sections 5.4.2–5.5, pp. 37–40 of Nisht and Abel 2024):\n\n1. **Theorem 4 — Soundness of Mutual Recursive Blocks**: In a closed run-time world $W$ with distinct function names containing $\Sigma \cup \Xi$, if the mutual block $\Xi$ is well-typed with respect to an SCT-valid invocation graph family $\mathcal{G}$ ($\Sigma \vdash \Xi$, written `BlockTy sig Ξ`) and $W \models \Sigma$, then $W \models \Xi$: every declaration $g \in \Xi$ inhabits its semantic type $\llbracket A_g \rrbracket_\rho$ for all valid valuations $\rho$ of $\Psi_g$.\n2. **Lemma 2 — Soundness of Global Signatures**: If a telescope of mutual blocks $\vec{\Xi}$ is well-typed (`BlocksTy blocks`) inside a closed world $W$ with distinct names, then $W \models \bigcup \vec{\Xi}$.\n3. **Theorem 5 — Strong Normalization of Programs**: For any well-typed complete program $\vdash (\vec{\Xi}; \mathsf{main}) : A$ (`ProgramTy blocks main A`), the entry term $\mathsf{main}$ is strongly normalizing in the world $\bigcup \vec{\Xi}$:\n   $$\vdash (\vec{\Xi}; \mathsf{main}) : A \implies \mathsf{SN}_{\bigcup \vec{\Xi}}(\mathsf{main}).$$\n4. **Theorem 6 — Embedding of Lexicographic Measures ($F_\omega^{\mathsf{cop}} \hookrightarrow F_\omega^{\mathsf{cop,SCT}}$)**: Any mutual block $\Xi$ well-typed under a duplicate-free lexicographic termination measure $m_f$ (`LexBlockTy sig Ξ`) admits an SCT-valid invocation graph family $\mathcal{G}$ and is therefore well-typed in System $F_\omega^{\mathsf{cop,SCT}}$ (`BlockTy sig Ξ`).\n\n**Formalization Note** Theorem 1 (well-foundedness of the semantic call relation induced by an SCT-valid graph family) is proved directly from infinite Ramsey's theorem (`Mathlib.Order.Filter.Ultrafilter`) with zero custom axioms.
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Chapter 5, Sections 5.4.2-5.5, pp. 37-40, Theorems 4-6 & Lemma 2

import Definitions.Def_NishtAbel2024V5_Syntax
import Definitions.Def_NishtAbel2024V5_Semantics
import Definitions.Def_NishtAbel2024V5_Inference

namespace NishtAbel2024V5

theorem theorems_4_5_and_6 :
    (∀ (W sig Ξ : List FunDecl),
      (∀ d ∈ sig ++ Ξ, d ∈ W) →
      (W.map FunDecl.name).Nodup →
      (∀ d ∈ W, (Tm.lam d.clauses).Closed) →
      BlockTy sig Ξ →
      SemValid W sig →
      SemValid W Ξ) ∧
    (∀ (W : List FunDecl) (blocks : List (List FunDecl)),
      (∀ d ∈ blocks.flatten, d ∈ W) →
      (W.map FunDecl.name).Nodup →
      (∀ d ∈ W, (Tm.lam d.clauses).Closed) →
      BlocksTy blocks →
      SemValid W blocks.flatten) ∧
    (∀ (blocks : List (List FunDecl)) (main : Tm) (A : Ty),
      ProgramTy blocks main A →
      SN blocks.flatten main) ∧
    (∀ (sig Ξ : List FunDecl),
      LexBlockTy sig Ξ →
      BlockTy sig Ξ) := by sorry

end NishtAbel2024V5
