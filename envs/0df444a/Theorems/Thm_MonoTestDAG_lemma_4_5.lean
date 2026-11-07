-- Prove2me | Theorems.Thm_MonoTestDAG_lemma_4_5
-- name    : MonoTestDAG.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:09:45.032675+00:00
-- url     : https://prove2.me/theorems/3eefe578-8ea5-4bfe-807a-d21a2e9e839c
-- title:
--   Lemma 4.5 — many violations in the NO distribution
-- statement:
--   In the setting of §4.3, with an $(s,4\varepsilon)$-PMRS witness on $|L|=|R|=n_0$, fix $i\in[s]$ and draw $F^-_i\sim D^-_i$. Then:
--
--   1. an edge $e=(\ell,r)\in M_i$ is violated by $F^-_i$ iff $Z_e\ne0$;
--   2. the violating edges contain a matching of size $X_i:=|\{e\in M_i:Z_e\ne0\}|$;
--   3. $X_i\sim\mathrm{Bin}(|M_i|,3/4)$;
--   4. if $X_i>2\varepsilon n_0$, then $F^-_i$ is $\varepsilon$-far from monotone;
--   5. for all sufficiently large $\varepsilon n_0$,
--   $$
--   \Pr[X_i>2\varepsilon n_0]\ge1-\exp(-\Omega(\varepsilon n_0))\ge\frac9{10}.
--   $$
--
--   This is the soundness half of the YES/NO construction.
--
--   Differences from the source:
--   - encoding: Ω(εn₀) and "sufficiently large εn₀" → absolute constants c > 0 and K before the graph; reason: Lean form of the page's absolute constants
--   - encoding: X_i ∼ Bin(|M_i|, 3/4) → the law of `noiseCount` equals the pushforward of `PMF.binomial` from `Fin (|M_i|+1)` to ℕ; reason: same distribution
--   - reading: s ∈ ℕ in Definition 4.3 → s ≥ 1, inside `IsPMRSWitness`; reason: [K] is defined only for positive K (p.1); the index i ∈ [s] and Unif([s]) need s ≥ 1
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Lemma 4.5, p.19

import Mathlib
import Definitions.Def_MonoTestDAG_dmon
import Definitions.Def_MonoTestDAG_IsPMRSWitness
import Definitions.Def_MonoTestDAG_yesDist

namespace MonoTestDAG

/-- **Lemma 4.5 (Many violations in the NO distribution).** In the setting of §4.3 (an
`(s, 4ε)`-PMRS witness `M` for `U = (L, R; E)` with `|L| = |R| = n₀`, positivity weights `w_i`),
fix `i ∈ [s]` and draw `F⁻_i ∼ D⁻_i`. Then
1. an edge `e = (ℓ, r) ∈ M_i` is violated by `F⁻_i` iff `Z_e ≠ 0`;
2. the violating edges contain a matching of size `X_i := |{e ∈ M_i : Z_e ≠ 0}|`;
3. `X_i ∼ Bin(|M_i|, 3/4)`;
4. if `X_i > 2εn₀`, then `F⁻_i` is `ε`-far from monotone;
5. since `|M_i| ≥ 4εn₀`, for all sufficiently large `εn₀`,
   `Pr[X_i > 2εn₀] ≥ 1 − exp(−Ω(εn₀)) ≥ 9/10`.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Lemma 4.5, p.19.

**Formalization Note.** The constants of `Ω(·)` and of "sufficiently large" (`c` and `K`) are
absolute. The law of `X_i` is compared with Mathlib's `PMF.binomial` on `{0, …, |M_i|}`. -/
theorem lemma_4_5 :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ {L R : Type} [Fintype L] [Fintype R] [DecidableEq L]
      [DecidableEq R] (EU : Finset (L × R)) (ε : ℝ) (s : ℕ) (M : Fin s → Finset (L × R)),
      IsPMRSWitness EU (4 * ε) s M → ∀ (w : Fin s → L ⊕ R → ℝ),
      (∀ i, IsPosWeight EU (M i) (w i)) → ∀ i : Fin s,
      (∀ (Z : ↥(M i) → Fin 4) (e : ↥(M i)),
          noFn (M i) (w i) Z (.inr e.1.2) < noFn (M i) (w i) Z (.inl e.1.1) ↔ Z e ≠ 0) ∧
      (∀ Z : ↥(M i) → Fin 4, ∃ N : Finset (L × R),
          OAI.SeymourSecondNeighborhood.Bipartite.IsMatching (fun l r => (l, r) ∈ EU) N ∧
          N.card = noiseCount (M i) Z ∧
          ∀ e ∈ N, noFn (M i) (w i) Z (.inr e.2) < noFn (M i) (w i) Z (.inl e.1)) ∧
      (noiseLaw (M i)).map (noiseCount (M i)) =
          (PMF.binomial (3 / 4) (by rw [div_le_one (by norm_num)]; norm_num) (M i).card).map (fun k => (k : ℕ)) ∧
      (∀ Z : ↥(M i) → Fin 4, 2 * ε * (Fintype.card L : ℝ) < (noiseCount (M i) Z : ℝ) →
          IsFar (bipDAG EU) ε (noFn (M i) (w i) Z)) ∧
      (K ≤ ε * (Fintype.card L : ℝ) →
          ENNReal.ofReal (1 - Real.exp (-(c * (ε * (Fintype.card L : ℝ))))) ≤
            (noiseLaw (M i)).toOuterMeasure
              {Z | 2 * ε * (Fintype.card L : ℝ) < (noiseCount (M i) Z : ℝ)} ∧
          (9 / 10 : ENNReal) ≤ (noiseLaw (M i)).toOuterMeasure
              {Z | 2 * ε * (Fintype.card L : ℝ) < (noiseCount (M i) Z : ℝ)}) := by sorry

end MonoTestDAG
