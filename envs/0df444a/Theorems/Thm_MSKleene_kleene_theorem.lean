-- Prove2me | Theorems.Thm_MSKleene_kleene_theorem
-- name    : MSKleene.kleene_theorem
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:38:00.690199+00:00
-- url     : https://prove2.me/theorems/f345dcc0-2d69-4bd4-9dd1-8e8902fc0e3c
-- title:
--   The many-sorted Kleene theorem
-- statement:
--   **The many-sorted Kleene theorem** (Theorem 4.22).
--
--   Let $S$ be a finite set of sorts, $\Sigma$ a finite $S$-sorted signature, and $X$ a finite $S$-sorted set of variables. Then for every sort $s \in S$,
--
--   $$\mathrm{Rec}_s(\mathbf{T}_\Sigma(X)) \;=\; \mathrm{Reg}_s(\mathbf{T}_\Sigma(X)),$$
--
--   that is, a language of sort $s$ in the free many-sorted algebra $\mathbf{T}_\Sigma(X)$ is $s$-recognizable — the preimage of a subset of a finite $\Sigma$-algebra under a homomorphism — if and only if it is $s$-regular — denoted by a regular expression built from the operations of $\Sigma$ together with empty language, union, sortwise substitution, and sortwise iteration.
--
--   The inclusion $\mathrm{Reg}_s \subseteq \mathrm{Rec}_s$ follows from the closure properties of recognizability (Corollary 4.8); the converse $\mathrm{Rec}_s \subseteq \mathrm{Reg}_s$ (Proposition 4.10) is proved by a constructive state-elimination argument carrying a sortwise budget (Main Claim 4.13).
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026, https://arxiv.org/abs/1808.08217 (predecessor CVCL20)

import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_Regular

namespace MSKleene

theorem kleene_theorem {S : Type} [Finite S] (sig : Signature S) (X : SSet S)
    (hsig : SigFinite sig) (hX : SFinite X) (s : S) :
    RecS (freeAlgebra sig X) s = RegS sig X s := by
  sorry

end MSKleene
