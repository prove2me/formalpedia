-- Prove2me | Theorems.Thm_MSKleene_subterm_wf
-- name    : MSKleene.subterm_wf
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:30:14.469141+00:00
-- url     : https://prove2.me/theorems/39363a4d-53de-47f0-9578-3afc894fa0fb
-- title:
--   Proposition 3.6: the subterm order is Artinian
-- statement:
--   **The subterm order is artinian** (Proposition 3.6).
--
--   The order $\le_{\mathbf{T}_{\Sigma}(X)}$ has no strictly descending $\omega_{0}$-chains, i.e. it is Artinian. Moreover $\mathrm{Min}(\coprod\mathrm{T}_{\Sigma}(X),\le_{\mathbf{T}_{\Sigma}(X)})$ is exactly $\{(x,s)\mid s\in S,\ x\in X_{s}\}\cup\{(\sigma^{\mathbf{T}_{\Sigma}(X)},s)\mid s\in S,\ \sigma\in\Sigma_{\lambda,s}\}$: the variables and the constant symbols.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_Subterm

namespace MSKleene

/-- **The subterm order is Artinian** (Proposition 3.6).

On the free algebra `T_Σ(X)` the strict proper-subterm order `SubtermLT` is
well-founded, and a sorted term is minimal for it iff it is a variable or a
constant symbol. -/
theorem subterm_wf {S : Type} (sig : Signature S) (X : SSet S) :
    WellFounded (SubtermLT (sig := sig) (X := X))
  ∧ ∀ b : STerm sig X, Min b ↔
      ((∃ x : X b.1, b.2 = Term.var x)
       ∨ (∃ σ : sig [] b.1, b.2 = Term.app σ TermVec.nil)) := by
  sorry

end MSKleene
