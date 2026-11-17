-- Prove2me | Theorems.Thm_GroupIsoPoly_Supplement_theorem_C_9
-- name    : GroupIsoPoly.Supplement.theorem_C_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:31:23.797432+00:00
-- url     : https://prove2.me/theorems/69c70ff9-073c-4694-b436-315a0c7487f3
-- title:
--   Theorem C.9, p.146 — $H^1(G,B)=H^1(G,B/C)=0$ for matrix modules of stable classical groups in odd characteristic
-- statement:
--   Let $p$ be an odd prime and let $G=\prod_{i<t}G_i$ be a product of derived classical groups $\mathrm{SL}$, $\mathrm{Sp}$, $\mathrm{SU}$, $\Omega$ over finite fields $K_i$ of characteristic $p$, in their natural representations and in the stable range. Let
--
--   $$B=\bigoplus_{j<s}\mathrm{Hom}_{L_j}(X_j,Y_j)$$
--
--   be a direct sum of full spaces of linear maps, where each $L_j$ is a finite field of characteristic $p$ and each $X_j,Y_j$ is a natural, dual, Frobenius-twisted natural, or trivial module (of one factor of $G$, viewed over $L_j$ by restriction of scalars), with $G$ acting by $g\cdot A=\rho_{Y_j}(g)A\rho_{X_j}(g)^{-1}$; $B$ is viewed over $\mathbb F_p$. Then for every $\mathbb F_p$-subspace $C$ of the fixed points $B^G$,
--
--   $$H^1(G,B)=H^1(G,B/C)=0 .$$
--
--   That is, every 1-cocycle $c:G\to B$ is a coboundary $c(g)=g\cdot b-b$, and the same holds for every 1-cocycle with values in $B/C$.
--
--   In the paper this provides the vanishing of first cohomology for the odd-characteristic target models (Definition 14) used to remove translations in degree-two tensor modules.
--
--   **Formalization Note** Each $X_j,Y_j$ is given by matrices over $L_j$ satisfying `IsC9Module`; $C$ ranges over additive subgroups of $B$ fixed pointwise by $G$.
--
--   Differences from the source:
--   - reading: "full spaces of linear maps between … modules, viewed over Fp by restriction of scalars" → B = ⊕_j Hom_{L_j}(X_j, Y_j) for finite fields L_j of characteristic p, each X_j, Y_j realized over L_j after restriction of scalars along an embedding L_j → K_i, as matrices Mat(dim Y_j × dim X_j, L_j); reason: Definition 14 ("Bj = Hom_Kj(Xj, Yj) … with restriction of scalars where required"); B is then viewed as an F_p-module
--   - encoding: trivial modules → the trivial line L_j; reason: Hom spaces from or to a trivial module of dimension k are k copies of the line case, a direct sum of the allowed summands
--   - encoding: "For every Fp-subspace C ≤ B^G" → every additive subgroup C of B fixed pointwise by G; reason: B has characteristic p, so its F_p-subspaces are exactly its additive subgroups
--   - encoding: H¹(G, B/C) → cocycles and coboundaries modulo C, on representatives in B; reason: a function to the quotient always lifts
--   - encoding: g · A = ρ_Y(g) A ρ_X(g)^{−1} → ρ_Y(g) A ρ_X(g⁻¹); reason: ρ_X is a representation, so ρ_X(g⁻¹) = ρ_X(g)^{−1}
--   - encoding: G a product of the stable natural derived classical groups → ∏ classicalGroup (dat i) over finite fields K_i of characteristic p (fields may differ), IsStableDerived; reason: §6.1 and Remark 1
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem C.9, p.146 (PDF p.150); Definition 14, p.46 (PDF p.50)

import Mathlib
import Definitions.Def_GroupIsoPoly_Supplement_IsStableDerived
import Definitions.Def_GroupIsoPoly_Supplement_homAct

set_option autoImplicit false

namespace GroupIsoPoly

namespace Supplement

/-- **Theorem C.9 (First cohomology of matrix modules in odd characteristic).**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem C.9, p.146 (PDF p.150): "Let G be a product of
the stable natural derived classical groups in odd characteristic p. Let B be a direct sum of full
spaces of linear maps between natural, dual, Frobenius-twisted natural, and trivial modules, viewed
over Fp by restriction of scalars. For every Fp-subspace C ≤ B^G, H1(G, B) = H1(G, B/C) = 0."

Let `p` be an odd prime and `G = ∏_{i<t} G_i` a product of derived classical groups
`G_i ∈ {SL, Sp, SU, Ω}` over finite fields `K_i` of characteristic `p` (the fields may differ), each in
its natural representation and in the stable range. For `j < s` let `L_j` be a finite field of
characteristic `p` and `X_j`, `Y_j` modules over `L_j` each of which is the trivial line or, after
restriction of scalars to `L_j`, a natural, dual or Frobenius-twisted natural module of one factor
(`IsC9Module`), and let `B = ⊕_j Hom_{L_j}(X_j, Y_j)` with `g·A = ρ_{Y_j}(g) A ρ_{X_j}(g)⁻¹`. Then
1. `H¹(G, B) = 0`: every 1-cocycle `c(gh) = c(g) + g·c(h)` is `c(g) = g·b − b`;
2. `H¹(G, B/C) = 0` for every `F_p`-subspace `C` of the fixed points `B^G`, stated on representatives
   modulo `C`.

**Formalization Note.** `B` has characteristic `p`, so its `F_p`-subspaces are exactly its additive
subgroups; `C` ranges over all `AddSubgroup`s fixed pointwise by `G`. -/
theorem theorem_C_9 (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {t : ℕ} {K : Fin t → Type}
    [∀ i, Field (K i)] [∀ i, Fintype (K i)] [∀ i, CharP (K i) p] {n : Fin t → ℕ}
    (dat : (i : Fin t) → ClassicalDatum (K i) (n i)) (hst : ∀ i, IsStableDerived (dat i))
    {s : ℕ} {L : Fin s → Type} [∀ j, Field (L j)] [∀ j, Fintype (L j)] [∀ j, CharP (L j) p]
    {aX aY : Fin s → ℕ}
    (ρX : (j : Fin s) → ClProd dat → Matrix (Fin (aX j)) (Fin (aX j)) (L j))
    (ρY : (j : Fin s) → ClProd dat → Matrix (Fin (aY j)) (Fin (aY j)) (L j))
    (hX : ∀ j, IsC9Module dat (ρX j)) (hY : ∀ j, IsC9Module dat (ρY j)) :
    (∀ c : ClProd dat → (j : Fin s) → Matrix (Fin (aY j)) (Fin (aX j)) (L j),
      (∀ g h, c (g * h) = c g + homAct ρX ρY g (c h)) →
      ∃ b, ∀ g, c g = homAct ρX ρY g b - b) ∧
    ∀ C : AddSubgroup ((j : Fin s) → Matrix (Fin (aY j)) (Fin (aX j)) (L j)),
      (∀ x ∈ C, ∀ g, homAct ρX ρY g x = x) →
      ∀ c : ClProd dat → (j : Fin s) → Matrix (Fin (aY j)) (Fin (aX j)) (L j),
        (∀ g h, c (g * h) - c g - homAct ρX ρY g (c h) ∈ C) →
        ∃ b, ∀ g, c g - (homAct ρX ρY g b - b) ∈ C := by sorry

end Supplement

end GroupIsoPoly
