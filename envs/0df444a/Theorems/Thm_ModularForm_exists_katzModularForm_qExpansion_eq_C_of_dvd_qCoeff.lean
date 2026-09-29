-- Prove2me | Theorems.Thm_ModularForm_exists_katzModularForm_qExpansion_eq_C_of_dvd_qCoeff
-- name    : ModularForm.exists_katzModularForm_qExpansion_eq_C_of_dvd_qCoeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/abcc90d1-273a-5648-8f39-99f8d88f1cfb
-- title:
--   Weight-two Γ₀(p) form congruent to a constant modulo m
-- statement:
--   Let $p$ be a prime and let $m$ be a natural number with $\gcd(p,m)=1$ (so $m\neq 0$). Let $h$ be a holomorphic modular form of weight $2$ for the congruence subgroup $\Gamma_0(p)$, in Mathlib's sense, and let $b:\mathbb N\to\mathbb Z$ be a sequence of integers whose images in $\mathbb C$ are the coefficients of the $q$-expansion of $h$ at the cusp $\infty$: for every $n$, $(b_n:\mathbb C)=\mathtt{qCoeff}\,h\,n$, the $n$-th coefficient of the width-one $q$-expansion of $h$. Assume $m\mid b_n$ in $\mathbb Z$ for every $n\neq 0$. The conclusion is that there exists a Katz modular form $F$ of weight $2$ over the ring $\mathbb Z/m$, that is, a rule assigning to each $\mathbb Z/m$-algebra $A$ and each Weierstrass curve $W$ over $A$ with $\Delta_W$ a unit an element $F(W)\in A$, compatible with $\mathbb Z/m$-algebra homomorphisms under base change of Weierstrass equations, and satisfying $F(C\cdot W)=(u_C^{-1})^{2}F(W)$ for every variable change $C$ with scaling unit $u_C$, whose $q$-expansion — its value on the Tate curve [`ModularCurve.tateLaurent`](def/ModularCurve_TateFormal.html#L86) over the Laurent series ring $(\mathbb Z/m)((q))$, obtained from the Tate Weierstrass equation over $\mathbb Z[[q]]$ by base change — is the constant Laurent series with value $b_0 \bmod m$.
--
--   This is the arithmetic content of Mazur's level-reduction step (Modular curves and the Eisenstein ideal, II, Lemmas 4.5, 4.7 and 5.9): a weight-two form on $\Gamma_0(p)$ with integral $q$-expansion congruent to a constant modulo $m$, with $m$ prime to $p$, descends to a level-one Katz form of weight $2$ over $\mathbb Z/m$ with that constant $q$-expansion. It is used to derive divisibility constraints on the constant term, as in the deduction that $9 \mid b_n$ for all $n \ge 1$ forces $3 \mid b_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_katzModularForm_qExpansion_eq_C_of_dvd_qCoeff.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_KatzLevelOne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.exists_katzModularForm_qExpansion_eq_C_of_dvd_qCoeff (p : ℕ) [Fact p.Prime]
    (m : ℕ) (hm : p.Coprime m) (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n)
    (hdvd : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ b n) :
    ∃ F : KatzModularForm (ZMod m) 2, F.qExpansion = HahnSeries.C ((b 0 : ℤ) : ZMod m) := by sorry
