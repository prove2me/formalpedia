-- Prove2me | Theorems.Thm_MSKleene_term_char
-- name    : MSKleene.term_char
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:29:45.913046+00:00
-- url     : https://prove2.me/theorems/b4978040-8cf3-4679-919f-04e0d595af1d
-- title:
--   Proposition 3.4: unique readability of terms
-- statement:
--   **Unique readability of terms** (Proposition 3.4).
--
--   For every sort $s\in S$ and every $P\in\mathrm{T}_{\Sigma}(X)_{s}$, exactly one of the following holds, and the data is unique in each case: (1) $P=x$ for a unique variable $x\in X_{s}$; (2) $P=\sigma^{\mathbf{T}_{\Sigma}(X)}$ for a unique constant symbol $\sigma\in\Sigma_{\lambda,s}$; (3) $P=\sigma^{\mathbf{T}_{\Sigma}(X)}((P_{j})_{j})$ for a unique non-empty arity $\mathbf{s}$, a unique $\sigma\in\Sigma_{\mathbf{s},s}$, and a unique family $(P_{j})_{j}$.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_Term

namespace MSKleene

/-- **Unique readability of terms** (Proposition 3.4).

For every sort `s` and every term `P ∈ T_Σ(X)_s`, there is a unique
decomposition belonging to exactly one of the following cases:
1. `P = var x` for a unique variable `x ∈ X_s`;
2. `P = app σ .nil` for a unique constant symbol `σ ∈ Σ_{[],s}`;
3. `P = app σ ts` for a unique non-empty arity `w`, a unique `σ ∈ Σ_{w,s}`, and
   a unique argument vector `ts`. -/
theorem term_char {S : Type} (sig : Signature S) (X : SSet S) {s : S}
    (P : Term sig X s) :
    ∃! c : X s ⊕ (sig [] s ⊕ ((w : List S) × sig w s × TermVec sig X w)),
      match c with
      | .inl x => P = Term.var x
      | .inr (.inl σ) => P = Term.app σ TermVec.nil
      | .inr (.inr p) => p.1 ≠ [] ∧ P = Term.app p.2.1 p.2.2 := by
  sorry

end MSKleene
