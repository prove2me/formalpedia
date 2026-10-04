-- Prove2me | Theorems.Thm_MSKleene_singleton_term_regular
-- name    : MSKleene.singleton_term_regular
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:37:18.535162+00:00
-- url     : https://prove2.me/theorems/f73e0b9c-a90f-4b1a-90d5-216ba136ae9b
-- title:
--   Lemma 4.9: every singleton of a term is regular
-- statement:
--   **Every singleton of a term is regular** (Lemma 4.9).
--
--   Let $s\in S$ and $P\in\mathrm{T}_{\Sigma}(X)_{s}$. Then $P\in\mathrm{T}_{\mathrm{Reg}(S,\Sigma,X)}(X)_{s}$ and $\{P\}^{X\sharp}_{s}=\{P\}$. Consequently $\{P\}\in\mathrm{Reg}_{s}(\mathbf{T}_{\Sigma}(X))$.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_Regular

namespace MSKleene

/-- **Every singleton of a term is regular** (Lemma 4.9).

For finite `S`, `Σ`, and `X`, every `P ∈ T_Σ(X)_s`, viewed as a regular
expression over `(S,Σ,X)`, denotes exactly `{P}`. Consequently, `{P}` is an
`s`-regular language. -/
theorem singleton_term_regular {S : Type} [Finite S]
    (sig : Signature S) (X : SSet S) (hsig : SigFinite sig) (hX : SFinite X)
    {s : S} (P : Term sig X s) :
    interpExpr sig X s (Term.toReg P) = {P}
  ∧ {P} ∈ RegS sig X s := by
  sorry

end MSKleene
