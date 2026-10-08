-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_encoded_witness_sum_le
-- name    : OAI.TwoPointCorrelations.encoded_witness_sum_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:14:11.09484+00:00
-- url     : https://prove2.me/theorems/82aff1ee-8f13-46c0-8b39-1f9e0252fdd3
-- title:
--   Counting weighted prime words with witnesses through crude word codes
-- statement:
--   Let $R,T,n,K,M,m_0,h,s,J$ be naturals (with $m_0$ = `mainLength`), `start`, `len` maps $\{1..n\}\to\mathbb N$, $P,Q$ finite sets of naturals and `supply` a binary relation on $\mathbb N$. Suppose $R\le M$, $8K\le n$, every element of $P$ is prime, $\sum_{p\in P}1/p\ge1$, and there are naturals $H\ge1$, $B\ge1$ with $H\le p\le B$ for every $p\in P$ and $\delta:=H^{-1}+(1+\log B)/H\le1$. Then the total weight of the prime word encodings that admit witnesses satisfies
--
--   $$\sum_{\substack{e\in\texttt{PrimeWordEncoding }R\,T\,P\,Q\\ e\text{ witnesses}}}\mathrm{wt}(e)\le\Big(\sum_{t=0}^{T}\sum_{c\in\texttt{CrudeWordCode }R\,t\,R}\#\texttt{WitnessSystemData}(n,M,c)\;V_P^{\#\mathrm{tuple}(c)}\;V_Q^{\#\mathrm{used}(c)\setminus\mathrm{tuple}(c)}\Big)\,\delta^{K},$$
--
--   where "witnesses" is `e.Witnesses n mainLength start len h s J supply`, $V_P=\sum_{p\in P}1/p$ and $V_Q=\sum_{q\in Q}1/q$ (`primeHarmonicMass`), and $\#\mathrm{tuple}(c)$, $\#\mathrm{used}(c)\setminus\mathrm{tuple}(c)$ count the tuple classes and the other used classes of the code. All named types are bundle definitions.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.encoded_witness_sum_le`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open scoped Classical

theorem encoded_witness_sum_le (R T n K M mainLength h s J : ℕ)
    (start len : Fin n → ℕ) (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop)
    (hRM : R ≤ M) (hsize : 8 * K ≤ n)
    (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B)
    (hdelta : (H : ℝ)⁻¹ + (1 + Real.log B) / H ≤ 1) :
    (∑ e : PrimeWordEncoding R T P Q,
      if e.Witnesses n mainLength start len h s J supply then e.weight else 0) ≤
      (∑ t : Fin (T + 1), ∑ c : CrudeWordCode R t.val R,
        (Fintype.card (WitnessSystemData n M c.tupleClasses) : ℝ) *
          primeHarmonicMass P ^ Fintype.card c.tupleClasses *
          primeHarmonicMass Q ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses}) *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) ^ K := by
  sorry

end OAI.TwoPointCorrelations
