-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_extra_prime_mean_square
-- name    : OAI.TwoPointCorrelations.mrt_extra_prime_mean_square
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:18.337155+00:00
-- url     : https://prove2.me/theorems/97d0a790-670e-42e1-a318-604739a39f8e
-- title:
--   Mean-square approximation of a dyadic polynomial by binned prime polynomials times cofactor polynomials (Ramaré identity)
-- statement:
--   Let $J$ be a finite index set with sets of primes $P_j$ ($j\in J$), $A$ a finite set of primes disjoint from $\bigcup_jP_j$, $K$ a finite set of bins with a bin map sending $A$ into $K$, lower endpoints $\ell:K\to\mathbb R$, $N\ge1$, and $\delta\in[1,2]$ with $\ell(\mathrm{bin}(p))\le p\le\delta\,\ell(\mathrm{bin}(p))$ for $p\in A$. Let $F$ be multiplicative (on coprime positive arguments) and bounded by $1$ on positive integers, $G$ = `mrtTypicalCoefficient J P F` ($F(n)$ if each $P_j$ contains a prime divisor of $n$, else $0$), and $T>0$. Then
--
--   $$\int_{-T}^{T}\Big|D_N(G_A,t)-\sum_{k\in K}\mathcal P_k(t)\,\mathcal C_k(t)\Big|^2dt\le1408e\Big(\frac TN+1\Big)\Big(\sum_{p\in A}\frac1{p^2}+\Big(\sum_{p\in A}\frac1{p^2}\Big)^2+(\delta-1)\Big),$$
--
--   where $G_A$ = `mrtSupportedCoefficient A G` is $G$ on integers with a prime factor in $A$ and $0$ elsewhere, $D_N(b,t)=\sum_{N<n\le2N}\frac{b(n)}nn^{-it}$ (`mrtDyadicPolynomial`), $\mathcal P_k(t)=\sum_{p\in A,\ \mathrm{bin}(p)=k}\frac{F(p)}pp^{-it}$, and $\mathcal C_k(t)$ = `mrtCofactorPolynomial A G N (ℓ k) t` $=\sum_{1\le m\le4N,\ N<\ell(k)m\le2N}\frac{G(m)m^{-1-it}}{\#\{p\in A:p\mid m\}+1}$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_extra_prime_mean_square`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open MeasureTheory
open scoped Classical

theorem mrt_extra_prime_mean_square {ι κ : Type*} [DecidableEq κ]
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (hout : Disjoint A (J.biUnion P))
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ A, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ A, lower (bin p) ≤ p ∧ (p:ℝ) ≤ δ*lower (bin p))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
      ‖mrtDyadicPolynomial (mrtSupportedCoefficient A (mrtTypicalCoefficient J P F)) N t -
        ∑ k ∈ K, mrtExponentialPolynomial (A.filter (fun p => bin p=k))
          (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t *
          mrtCofactorPolynomial A (mrtTypicalCoefficient J P F) N (lower k) t‖^2) ≤
      1408*Real.exp 1*(T/(N:ℝ)+1)*
        ((∑ p ∈ A, 1/(p:ℝ)^2)+(∑ p ∈ A, 1/(p:ℝ)^2)^2+(δ-1)) := by
  sorry

end OAI.TwoPointCorrelations
