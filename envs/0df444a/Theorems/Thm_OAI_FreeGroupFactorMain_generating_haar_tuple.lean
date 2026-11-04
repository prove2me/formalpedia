-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_generating_haar_tuple
-- name    : OAI.FreeGroupFactorMain.generating_haar_tuple
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T03:08:18.408481+00:00
-- url     : https://prove2.me/theorems/88125034-fc36-43cc-b8b9-9ddca7ebf66f
-- title:
--   Freely generating Haar tuple of rank n in L(F_{n+1}), n at least three
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $n\ge3$ and $M=L(\mathbb F(\mathrm{Fin}\,n\sqcup\{*\}))$. There is an $n$-tuple $U$ of unitaries in $M$ with $\tau(U_g)=0$ for every nonidentity $g\in\mathbb F_n$, and such that the vectors $U_g\delta_e$ have dense linear span in $\ell^2(\mathbb F(\mathrm{Fin}\,n\sqcup\{*\}))$:
--
--   $$\overline{\mathrm{span}}\{U_g\delta_e:g\in\mathbb F_n\}=\ell^2.$$
--
--   This plays the role of the limit tuple constructed in the proof of Theorem 1.1 of the paper, and Lean obtains it by a Baire-type lemma rather than an explicit iteration; Lemma 2.2 then gives $L(\mathbb F_n)\cong L(\mathbb F_{n+1})$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.generating_haar_tuple`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/Generation.lean#L327

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe uA uB uC uG uH uI uK uP uX uY uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation

section
variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B] {ι : Type uι} {κ : Type uκ}

end

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain

open Generation

theorem generating_haar_tuple (n : ℕ) (hn : 3 ≤ n) :
    ∃ U : Tuple n,
      (∀ g : FreeGroup (Fin n), canonicalTrace (word U g) = if g = 1 then 1 else 0) ∧
      ⊤ ≤ (Submodule.span ℂ (Set.range (fun g => groupL2 (word U g)))).topologicalClosure := by
  sorry

end FreeGroupFactorMain
end
end OAI
