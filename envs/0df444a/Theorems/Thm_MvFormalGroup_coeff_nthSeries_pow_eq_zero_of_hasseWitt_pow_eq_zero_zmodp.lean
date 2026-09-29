-- Prove2me | Theorems.Thm_MvFormalGroup_coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp
-- name    : MvFormalGroup.coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/c1ef1486-dd50-521c-a81f-ed6608cd8768
-- title:
--   Multiplication by p^ν when the Hasse–Witt matrix is ν-nilpotent
-- statement:
--   Let $p$ be a prime, $d$ a natural number, and let $F$ be a $d$-dimensional formal group law over $\mathbb{Z}/p$: a $d$-tuple $F_1,\dots,F_d$ of formal power series in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with vanishing constant term, with the coefficient of $X_{\mathrm{inl}\,j}$ and of $X_{\mathrm{inr}\,j}$ in $F_i$ equal to $\delta_{ij}$, and satisfying the associativity identity $F(F(X,Y),Z)=F(X,F(Y,Z))$ under substitution; assume moreover `F.IsComm`, i.e. interchanging the two blocks of variables leaves each $F_i$ unchanged. Write $[n]_F$ for the $d$-tuple `F.nthSeries n` of power series in $d$ variables defined by $[0]_F = 0$ and $[n+1]_F = F([n]_F, X)$. Let $\nu$ be a natural number and suppose that the $d\times d$ matrix over $\mathbb{Z}/p$ whose $(i,j)$ entry is the coefficient of the monomial $X_j^{p}$ in $[p]_{F,i}$ — the Hasse–Witt matrix — satisfies $B^{\nu}=0$. Then for every index $i$ and every multi-index $m : \mathrm{Fin}\,d \to_{f} \mathbb{N}$ such that $p^{\nu+1}$ fails to divide $m_j$ for at least one $j$, the coefficient of $X^m$ in $[p^{\nu}]_{F,i}$ vanishes.
--
--   In classical terms: over the prime field, $\nu$-fold nilpotence of the Hasse–Witt matrix forces the multiplication-by-$p^{\nu}$ endomorphism of $F$ to be a power series in the variables $X_1^{p^{\nu+1}},\dots,X_d^{p^{\nu+1}}$. The proof invokes the factorisation criterion [`MvFormalGroup.coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP`](thm.html#MvFormalGroup.coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP), which makes a homomorphism with vanishing linear part factor through the $p$-th power map in characteristic $p$, and the result feeds into [`MvFormalGroup.exists_forall_coeff_nthSeries_pow_mem_span_of_isNilpotent_hasseWitt`](thm.html#MvFormalGroup.exists_forall_coeff_nthSeries_pow_mem_span_of_isNilpotent_hasseWitt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MvPowerSeries

universe u

theorem MvFormalGroup.coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp
    (p : ℕ) [Fact p.Prime] {d : ℕ} (F : MvFormalGroup d (ZMod p)) [F.IsComm]
    (ν : ℕ)
    (hB : (Matrix.of fun i j : Fin d => (F.nthSeries p i).coeff (Finsupp.single j p)) ^ ν = 0)
    (i : Fin d) (m : Fin d →₀ ℕ) (hm : ∃ j, ¬ p ^ (ν + 1) ∣ m j) :
    (F.nthSeries (p ^ ν) i).coeff m = 0 := by sorry
