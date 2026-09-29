-- Prove2me | Theorems.Thm_KatzModularForm_exists_qExpansion_eq_C_of_dvd
-- name    : KatzModularForm.exists_qExpansion_eq_C_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/271a54fe-22fe-5c73-90d3-42ade38fc730
-- title:
--   Constant q-expansions of weight-two Katz forms mod m
-- statement:
--   Let $m$ be a natural number and $c$ an integer such that the integer $m/\gcd(m,12)$ (natural-number division) divides $c$. Then there is a Katz modular form $F$ of weight $2$ over the ring $\mathbb{Z}/m$ whose $q$-expansion is the constant Laurent series $c \bmod m$. Here a term of [`KatzModularForm (ZMod m) 2`](def/ModularForm_KatzLevelOne.html#L10) is, by definition, the data of a rule `toFun` assigning to every commutative $\mathbb{Z}/m$-algebra $A$ and every Weierstrass curve $W$ over $A$ whose discriminant $\Delta$ is a unit an element of $A$, subject to two axioms: compatibility with base change, i.e. for every $\mathbb{Z}/m$-algebra map $f : A \to B$ the value on the curve $W$ pushed forward along $f$ equals $f$ applied to the value on $W$; and, for every variable change $C = (u,r,s,t)$ over $A$, the value on $C \bullet W$ equals $(u^{-1})^{2}$ times the value on $W$. The $q$-expansion `qExpansion` of such an $F$ is its value on the Weierstrass curve [`ModularCurve.tateLaurent (ZMod m)`](def/ModularCurve_TateFormal.html#L86) over the Laurent series ring, that is the Tate curve obtained by base change from its integral model, at the witness that the discriminant of that curve is a unit; the assertion is that this Laurent series equals `HahnSeries.C (c : ZMod m)`.
--
--   This is the constructive half of Mazur's description of the weight-two level-one modular forms modulo $m$ with constant $q$-expansion: the constants that occur are exactly the multiples of $m/\gcd(m,12)$. It is used to produce Katz forms with prescribed constant $q$-expansion, via [`ModularForm.exists_katzModularForm_qExpansion_eq_C_of_dvd_qCoeff`](thm.html#ModularForm.exists_katzModularForm_qExpansion_eq_C_of_dvd_qCoeff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_KatzModularForm_exists_qExpansion_eq_C_of_dvd.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem KatzModularForm.exists_qExpansion_eq_C_of_dvd (m : ℕ) (c : ℤ)
    (hc : ((m / Nat.gcd m 12 : ℕ) : ℤ) ∣ c) :
    ∃ F : KatzModularForm (ZMod m) 2, F.qExpansion = HahnSeries.C (c : ZMod m) := by sorry
