-- Prove2me | Theorems.Thm_ModularCurve_exists_natCard_quot_samePlace_eq_natCard_quot_sameOrbit_of_EMD
-- name    : ModularCurve.exists_natCard_quot_samePlace_eq_natCard_quot_sameOrbit_of_EMD
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/0a563c37-7a87-58af-8b6c-686de94c8c62
-- title:
--   Class counts agree under the embedding–moduli dictionary at j₀
-- statement:
--   Let $N$ be a nonzero natural number and let $j_0 \in \overline{\mathbb{Q}}$, and assume the predicate [`ModularCurve.EMD N j₀`](def/ModularCurve_EMD.html#L46), i.e. that there is a Weierstrass curve $E_0$ over $\overline{\mathbb{Q}}$ which is elliptic, has $j$-invariant $j_0$, and admits a bijection $\Phi$ from [`ModularCurve.Emb N j₀`](def/ModularCurve_EMD.html#L22) onto [`ModularCurve.CycSub E₀ N`](def/ModularCurve_EMD.html#L36) such that two embeddings satisfy [`ModularCurve.SamePlace`](def/ModularCurve_EMD.html#L31) exactly when their images satisfy [`ModularCurve.SameOrbit`](def/ModularCurve_EMD.html#L40). Here `Emb N j₀` consists of the $\overline{\mathbb{Q}}$-algebra homomorphisms $\psi$ from the base-changed modular function field `modularFunctionFieldBar N` into the Hahn series $\mathrm{HahnSeries}\,\mathbb{Q}\,\overline{\mathbb{Q}}$ normalised by $\psi(\bar\jmath) = j_0 + t$; `SamePlace ψ ψ'` asserts the existence of one place $w$ of the field (a valuation subring, proper, containing the constants, a principal ideal ring) which both $\psi$ and $\psi'$ induce, in the sense that for each of them some positive rational $g$ satisfies $w.\mathrm{ord}(x)\cdot g = \mathrm{order}(\psi x)$ for all $x$; `CycSub E₀ N` consists of the additive subgroups of the affine point group of $E_0$ of the form $\mathbb{Z}g$ with $g$ of additive order $N$; and `SameOrbit E₀ H H'` asserts that $H = \mathbb{Z}g$, $H' = \mathbb{Z}g'$ with $g'$ the image of $g$ under `Point.vcInvFun` for some variable change $\gamma$ fixing $E_0$. The conclusion asserts the existence of an elliptic Weierstrass curve $E_0$ over $\overline{\mathbb{Q}}$ with $j(E_0) = j_0$ for which the quotient of `Emb N j₀` by the relation `SamePlace` and the quotient of `CycSub E₀ N` by the relation `SameOrbit` have equal `Nat.card`.
--
--   This is the numerical consequence extracted from the embedding–moduli dictionary at a fixed $j$-invariant: the moduli interpretation of level-$N$ structures identifies normalised embeddings of the modular function field modulo the place they induce with cyclic subgroups of order $N$ on an elliptic curve with that $j$-invariant, modulo the automorphisms of the curve. It is used by [`ModularCurve.card_eq_natCard_moduliPoint_j_eq_of_EMD`](thm.html#ModularCurve.card_eq_natCard_moduliPoint_j_eq_of_EMD) to count the points of the modular curve lying over a given $j$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_natCard_quot_samePlace_eq_natCard_quot_sameOrbit_of_EMD.lean

import Mathlib
import Definitions.Def_ModularCurve_EMD
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_natCard_quot_samePlace_eq_natCard_quot_sameOrbit_of_EMD (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ) (hEMD : ModularCurve.EMD N j₀) :
    ∃ (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E₀.IsElliptic), E₀.j = j₀ ∧
      Nat.card (Quot (fun ψ ψ' : ModularCurve.Emb N j₀ => ModularCurve.SamePlace ψ.1 ψ'.1))
        = Nat.card (Quot (fun H H' : ModularCurve.CycSub E₀ N => ModularCurve.SameOrbit E₀ H.1 H'.1)) := by sorry
