-- Prove2me | Theorems.Thm_MSKleene_rec_closed_reg
-- name    : MSKleene.rec_closed_reg
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:32:42.274991+00:00
-- url     : https://prove2.me/theorems/c675052b-567a-4d72-8e17-986785b0ca85
-- title:
--   Corollary 4.4: Rec is a closed subset of the regular algebra
-- statement:
--   **Rec is a closed subset of the regular algebra** (Corollary 4.4).
--
--   Let $Z$ be a finite $S$-sorted set. The $S$-sorted set $(\mathrm{Rec}_{s}(\mathbf{T}_{\Sigma}(Z)))_{s\in S}$ is a closed subset of the $\mathrm{Reg}(S,\Sigma,Z)$-algebra $\mathbf{T}^{\mathrm{Reg}}_{\Sigma}(Z)^{\wp}$: it is closed under every operation of $\mathrm{Reg}(S,\Sigma,Z)$ — the empty constant, union, $z$-iteration, $z$-substitution, and every $\sigma\in\Sigma$.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_RegAlgebra

namespace MSKleene

/-- **`Rec` is a closed subset of the regular algebra** (Corollary 4.4).

With `S` finite and `Z` a finite `S`-sorted set: for every symbol of
`Reg(S,Σ,Z)` and every tuple of `Z`-languages that are componentwise
recognizable, the interpreted regular operation on `T_Σ(Z)^℘` yields a
recognizable language. In particular `(Rec_s(T_Σ(Z)))_s` is closed under
`∅`, `+`, `z`-iteration, `z`-substitution, and every `σ ∈ Σ`. -/
theorem rec_closed_reg {S : Type} [Finite S] (sig : Signature S) (Z : SSet S)
    (hZ : SFinite Z) {w : List S} {s : S} (sym : regSig sig Z w s)
    (Ls : Args (fun s => Set (Term sig Z s)) w)
    (hLs : Args.All (fun s L => sRecognizable (freeAlgebra sig Z) s L) Ls) :
    sRecognizable (freeAlgebra sig Z) s ((regPowerAlgebra sig Z).op sym Ls) := by
  sorry

end MSKleene
