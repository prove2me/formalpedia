-- Prove2me | Theorems.Thm_MvFormalGroup_coeff_subst_iterate_sum_single_eq_constantCoeff_invariantDerivation_iterate
-- name    : MvFormalGroup.coeff_subst_iterate_sum_single_eq_constantCoeff_invariantDerivation_iterate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/28f5f06c-e0ae-5a05-ac64-e1e9c8d96ccf
-- title:
--   Iterated invariant derivation at the origin as a multilinear coefficient
-- statement:
--   Let $\mathcal O$ be a commutative ring, $d$ a natural number, and $F$ a $d$-dimensional formal group law over $\mathcal O$ in the sense of the project structure: a family `F.toPowerSeries` of $d$ power series in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$, each with vanishing constant term, with the coefficient of each single variable $X_{\mathrm{inl}\,j}$ and of each $X_{\mathrm{inr}\,j}$ in the $i$-th component equal to $1$ if $i=j$ and $0$ otherwise, and satisfying the associativity identity between the two threefold substitutions. Let $G$ assign to each $n$ a family $G\,n$ of $d$ power series in the variables indexed by $\mathrm{Fin}\,n \times \mathrm{Fin}\,d$, subject to $G\,1\,k = X_{(0,k)}$ for all $k$ and to the recursion: $G\,(n+1)\,k$ is obtained from the $k$-th component of $F$ by substituting for the $\mathrm{inl}$-variables the series $G\,n\,j$ with its variables $(s,t)$ relabelled as $(\mathrm{Fin.castSucc}\,s,t)$, and for the $\mathrm{inr}$-variables the variables $X_{(\mathrm{Fin.last}\,n,\,j)}$. Fix $i \in \mathrm{Fin}\,d$ and a map $L$ on $\mathcal O[[X_1,\dots,X_d]]$ such that for every $H$ and every exponent $a : \mathrm{Fin}\,d \to_{f} \mathbb N$, the coefficient of $a$ in $L\,H$ equals the coefficient of the exponent on $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with $\mathrm{inl}$-part $a$ and $\mathrm{inr}$-part $\mathrm{single}\,i\,1$ in $H(F)$, i.e. in the substitution of `F.toPowerSeries` into $H$. Then for every $n \ge 1$ and every power series $H$, the coefficient of the multilinear monomial $\sum_{s \in \mathrm{Fin}\,n} \mathrm{single}\,(s,i)\,1$ in the substitution of $G\,n$ into $H$ equals the constant coefficient of $L^{[n]}H$, the $n$-fold iterate of $L$ applied to $H$.
--
--   This is the standard identification of the coefficient of $X_i^{(0)}\cdots X_i^{(n-1)}$ in $H$ composed with the $n$-fold iterated group law with the value at the origin of the $n$-th power of the $i$-th invariant derivation, here formulated purely coefficientwise and for an arbitrary commutative ring of coefficients. It is used in the computation of powers of the invariant derivation in terms of Hasse–Witt data, through [`MvFormalGroup.exists_cartierDual_derivation_pow_eq_sum_hasseWitt_smul`](thm.html#MvFormalGroup.exists_cartierDual_derivation_pow_eq_sum_hasseWitt_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_coeff_subst_iterate_sum_single_eq_constantCoeff_invariantDerivation_iterate.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MvPowerSeries

universe u

theorem MvFormalGroup.coeff_subst_iterate_sum_single_eq_constantCoeff_invariantDerivation_iterate
    {𝓞 : Type u} [CommRing 𝓞] {d : ℕ} (F : MvFormalGroup d 𝓞)
    (G : (n : ℕ) → Fin d → MvPowerSeries (Fin n × Fin d) 𝓞)
    (hG1 : ∀ k, G 1 k = X ((0 : Fin 1), k))
    (hGsucc : ∀ (n : ℕ) (k : Fin d), G (n + 1) k =
      subst (Sum.elim
        (fun j => subst (fun sj : Fin n × Fin d => (X (Fin.castSucc sj.1, sj.2) :
          MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)) (G n j))
        (fun j => (X (Fin.last n, j) : MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)))
        (F.toPowerSeries k))
    (i : Fin d) (L : MvPowerSeries (Fin d) 𝓞 → MvPowerSeries (Fin d) 𝓞)
    (hL : ∀ (H : MvPowerSeries (Fin d) 𝓞) (a : Fin d →₀ ℕ),
      (L H).coeff a = (subst F.toPowerSeries H).coeff (a.sumElim (Finsupp.single i 1)))
    (n : ℕ) (hn : 1 ≤ n) (H : MvPowerSeries (Fin d) 𝓞) :
    (subst (G n) H).coeff (∑ s : Fin n, Finsupp.single (s, i) 1) = (L^[n] H).constantCoeff := by sorry
