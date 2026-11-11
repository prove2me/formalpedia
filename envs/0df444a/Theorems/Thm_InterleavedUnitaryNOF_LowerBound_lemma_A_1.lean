-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_lemma_A_1
-- name    : InterleavedUnitaryNOF.LowerBound.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:02.280535+00:00
-- url     : https://prove2.me/theorems/ca74e089-f0f6-4f71-bbbd-5aa23889a1d8
-- title:
--   Lemma A.1 — GoodCube, all four clauses
-- statement:
--   Fix $0<\epsilon<1$. There is $C_\epsilon>0$ depending only on $\epsilon$. For every $0<\eta<1/2$, integer $d\ge1$, nonempty finite $I,J,K$, and Boolean matrices $F:J\times K\to\{0,1\}$ and $G:I\times K\to\{0,1\}$ of density $\mathbb E G\ge2^{-d}$, GoodCube terminates and returns nonempty $I^*\subseteq I$, $K^*\subseteq K$ and a list $(I_i,J_i,K_i,F_i)$ with $I_i\subseteq I^*$, $J_i\subseteq J$, $K_i\subseteq K^*$ and zero-extended $F_i$ on $J_i\times K_i$. Put $G_i=G[I_i,K_i]$. Its outputs satisfy all four clauses:
--
--   1. $F(y,z)1_{K^*}(z)=\sum_iF_i(y,z)$ on $J\times K$.
--   2. Every $F_i$ has density at most $2^{-d}$, or both $F_i,G_i$ are $(\epsilon,d)$-regular and satisfy $\epsilon$-min-degree.
--   3. $\mathbb E G[I^*,K^*]\ge\mathbb E G$, and
--
--   $$\sum_i|I_i||J_i||K_i|\le(d+2)|I^*||J||K^*|,\qquad \sum_i|I^*\setminus I_i||J_i||K_i|\le\eta(d+2)|I^*||J||K^*|.$$
--
--   4. The selected rectangle and output count obey
--
--   $$|I^*||K^*|\ge e^{-C_\epsilon d^4/\eta}|I||K|,\qquad \ell\le e^{C_\epsilon d^3}.$$
--
--   All finite averages use normalized uniform measures on the stated subdomains.
--
--   Differences from the source:
--   - encoding: arbitrary nonempty finite sets and normalized uniform subdomain averages → full-space Boolean matrices interpreted on explicit Finset domains, with zero-extended outputs and cardinality-normalized sums; reason: every finite set is represented by a bijection, and the initial subsets are required nonempty
--   - encoding: termination and returned outputs of the finite recursive procedure → eventual stabilization of finite-budget execution to Some output, with no termination hypothesis; reason: fuel exhaustion is None, never a default successful output; stabilization asserts actual termination and output bounds together
--   - reading: GoodCube uses deterministic choices and cited regularity subroutines, with no running-time conclusion in Lemma A.1 → fixed finite-list selection and exhaustive density-increment rectangle search satisfying the cited Sift selection thresholds; reason: this resolves the unspecified choices; exact grid regularity is tested, no output certificate or final bound is searched or assumed
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Lemma A.1, printed p.19 = PDF p.19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_FiniteDecomposition

open MeasureTheory

namespace InterleavedUnitaryNOF.LowerBound

theorem lemma_A_1 (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : ℝ), 0 < η → η < (1 : ℝ)/2 →
      ∀ (d : ℕ), 1 ≤ d → ∀ (a b c : ℕ)
      (I : Finset (Fin a)) (J : Finset (Fin b)) (K : Finset (Fin c))
      (F : Fin b → Fin c → Bool) (G : Fin a → Fin c → Bool),
      I.Nonempty → J.Nonempty → K.Nonempty →
      Real.rpow 2 (-(d : ℝ)) ≤ finiteDensity I K G →
      ∃ (out : CubeOutput a b c) (fuel₀ : ℕ),
        (∀ fuel ≥ fuel₀, goodCube ε η d fuel I J K F G = some out) ∧
        out.Istar.Nonempty ∧ out.Kstar.Nonempty ∧ out.Istar ⊆ I ∧ out.Kstar ⊆ K ∧
        (∀ A ∈ out.pieces, A.I ⊆ out.Istar ∧ A.J ⊆ J ∧ A.K ⊆ out.Kstar ∧
          A.F = restrictMatrix A.J A.K A.F ∧ A.G = restrictMatrix A.I A.K G) ∧
        (∀ y z, bval ((restrictMatrix J out.Kstar F) y z) =
          (out.pieces.map (fun A => bval (A.F y z))).sum) ∧
        (∀ A ∈ out.pieces, finiteDensity A.J A.K A.F ≤ Real.rpow 2 (-(d : ℝ)) ∨
          (finiteRegular A.J A.K A.F ε d ∧ finiteRegular A.I A.K A.G ε d ∧
           finiteMinDegree A.J A.K A.F ε ∧ finiteMinDegree A.I A.K A.G ε)) ∧
        finiteDensity I K G ≤ finiteDensity out.Istar out.Kstar G ∧
        (out.pieces.map (fun A => (A.I.card : ℝ)*A.J.card*A.K.card)).sum ≤
          ((d : ℝ)+2)*out.Istar.card*J.card*out.Kstar.card ∧
        (out.pieces.map (fun A => ((out.Istar \ A.I).card : ℝ)*A.J.card*A.K.card)).sum ≤
          η*((d : ℝ)+2)*out.Istar.card*J.card*out.Kstar.card ∧
        Real.exp (-C*(d : ℝ)^4/η)*I.card*K.card ≤ (out.Istar.card : ℝ)*out.Kstar.card ∧
        (out.pieces.length : ℝ) ≤ Real.exp (C*(d : ℝ)^3) := by sorry

end InterleavedUnitaryNOF.LowerBound
