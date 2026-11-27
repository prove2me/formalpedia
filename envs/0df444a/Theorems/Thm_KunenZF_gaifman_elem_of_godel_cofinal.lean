-- Prove2me | Theorems.Thm_KunenZF_gaifman_elem_of_godel_cofinal
-- name    : KunenZF.gaifman_elem_of_godel_cofinal
-- status  : Proved
-- author  : @teargosling
-- created : 2026-11-27T05:06:09.517487+00:00
-- url     : https://prove2.me/theorems/7c366cb1-bbdb-465f-b8dd-7bd5e7657113
-- title:
--   Gaifman's Lemma in $\mathrm{ZF}(j)$: cofinal Gödel-preserving maps are elementary
-- statement:
--   Let $M$ be a nonempty model of $\mathrm{ZF}(j)$ in the expanded language $\{\in, j\}$ (that is, $\mathrm{ZF}$ with Separation and Collection extended to formulas mentioning $j$), and let $k : M \to M$ be a cofinal map that preserves membership and the 12 Gödel set operations (`IsGodelCofinalEmb k`). Then $k$ is fully elementary for every pure $\{\in\}$-formula $\varphi$ and every variable assignment $v : \mathbb{N} \to M$:
--
--   $$M \models \varphi[v] \iff M \models \varphi[k \circ v].$$
--
--   This is the $\mathrm{ZF}$ form of Gaifman's Lemma (1974): any cofinal $\Delta_0$-elementary embedding between models of $\mathrm{ZF}$ is automatically fully elementary, without invoking the Axiom of Choice. Because preservation of the 12 Gödel operations and cofinality form a single finite first-order condition, this lemma lets one express full elementarity of a definable class map inside $\mathrm{ZF}$, which is the key engine behind Suzuki's theorem on the non-definability of Reinhardt embeddings.
--
--   **Formalization Note:** The pure $\{\in\}$-formula $\varphi : \mathrm{SFormula}$ is embedded into the language $\{\in, j\}$ via `incl.onBoundedFormula`, and the finite Gödel-preservation and cofinality assumptions are packaged in `IsGodelCofinalEmb` from `Definitions.Def_KunenZF_godel`.
-- source:
--   Haim Gaifman, Elementary embeddings of models of set-theory and certain subtheories, in Axiomatic Set Theory, Proc. Sympos. Pure Math. XIII, Part II (1974), pp. 33-101, Theorem 1; Kurt Gödel, The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory, Annals of Mathematics Studies 3 (1940), Chapter II.

import Mathlib.ModelTheory.Semantics
import Definitions.Def_KunenZF_language
import Definitions.Def_KunenZF_theory
import Definitions.Def_KunenZF_godel
import Definitions.Def_CH_SetTheoryLanguage

universe u

open FirstOrder FirstOrder.Language

namespace KunenZF
theorem gaifman_elem_of_godel_cofinal {M : Type u} [setLangJ.Structure M] [Nonempty M]
    (hM : M ⊨ ZFj) (k : M → M) (hk : IsGodelCofinalEmb k)
    (φ : ContinuumHypothesis.SFormula) (v : ℕ → M) :
    Formula.Realize (incl.onBoundedFormula φ) v ↔
      Formula.Realize (incl.onBoundedFormula φ) (k ∘ v) := by sorry
end KunenZF
