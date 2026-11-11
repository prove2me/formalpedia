-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_lemma_A_2
-- name    : InterleavedUnitaryNOF.LowerBound.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:08.545958+00:00
-- url     : https://prove2.me/theorems/196fa74f-ab0c-4970-94ae-f08657eaae62
-- title:
--   Lemma A.2 — AB-decomposition bounds and sparse-or-regular classification
-- statement:
--   Fix $0<\epsilon<1$. There is $C_\epsilon>0$ depending only on $\epsilon$. For every integer $d\ge1$, nonempty finite $I,J,K$ and Boolean $F:J\times K\to\{0,1\}$, $G:I\times K\to\{0,1\}$, the first call of the source AB-decomposition, with depth counter $r=0$, terminates and returns a list of $L$ tuples $(I_i,J_i,K_i,F_i,G_i)$ satisfying
--
--   $$\sum_{i=1}^L|I_i||J_i||K_i|\le4(d+2)^2|I||J||K|,\qquad L\le\exp(C_\epsilon d^7).$$
--
--   Every output has a matrix of normalized density at most $2^{-d}$, or both matrices are $(\epsilon,d)$-regular and satisfy $\epsilon$-min-degree. The procedure uses $\eta=1/[4(d+2)^2]$, the stated residual and omitted-domain recursive calls, and both terminal cases, including singleton outputs when $|I||K|<2^d$.
--
--   Differences from the source:
--   - encoding: arbitrary nonempty finite sets and normalized uniform subdomain averages → full-space Boolean matrices interpreted on explicit Finset domains, with zero-extended outputs and cardinality-normalized sums; reason: every finite set is represented by a bijection, and the initial subsets are required nonempty
--   - encoding: termination and returned outputs of the finite recursive procedure → eventual stabilization of finite-budget execution to Some output, with no termination hypothesis; reason: fuel exhaustion is None, never a default successful output; stabilization asserts actual termination and output bounds together
--   - reading: GoodCube uses deterministic choices and cited regularity subroutines, with no running-time conclusion in Lemma A.1 → fixed finite-list selection and exhaustive density-increment rectangle search satisfying the cited Sift selection thresholds; reason: this resolves the unspecified choices; exact grid regularity is tested, no output certificate or final bound is searched or assumed
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Lemma A.2, printed p.20 = PDF p.20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_FiniteDecomposition

open MeasureTheory

namespace InterleavedUnitaryNOF.LowerBound

theorem lemma_A_2 (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (a b c : ℕ)
      (I : Finset (Fin a)) (J : Finset (Fin b)) (K : Finset (Fin c))
      (F : Fin b → Fin c → Bool) (G : Fin a → Fin c → Bool),
      I.Nonempty → J.Nonempty → K.Nonempty →
      ∃ (out : List (FinitePiece a b c)) (fuel₀ : ℕ),
        (∀ fuel ≥ fuel₀, abDecomposition ε d fuel 0 I J K F G = some out) ∧
        (out.map (fun A => (A.I.card : ℝ)*A.J.card*A.K.card)).sum ≤
          4*((d : ℝ)+2)^2*I.card*J.card*K.card ∧
        (out.length : ℝ) ≤ Real.exp (C*(d : ℝ)^7) ∧
        (∀ A ∈ out, finiteDensity A.J A.K A.F ≤ Real.rpow 2 (-(d : ℝ)) ∨
          finiteDensity A.I A.K A.G ≤ Real.rpow 2 (-(d : ℝ)) ∨
          (finiteRegular A.J A.K A.F ε d ∧ finiteRegular A.I A.K A.G ε d ∧
           finiteMinDegree A.J A.K A.F ε ∧ finiteMinDegree A.I A.K A.G ε)) := by sorry

end InterleavedUnitaryNOF.LowerBound
