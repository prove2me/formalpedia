-- Prove2me | Theorems.Thm_HardCoreLocalSampling_Local_effective_taylor_coefficients
-- name    : HardCoreLocalSampling.Local.effective_taylor_coefficients
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:56.186204+00:00
-- url     : https://prove2.me/theorems/1465ac9d-c21b-4398-b3da-43e3115fe26a
-- title:
--   Lemma 16 — Effective Taylor coefficients
-- statement:
--   Fix $\Delta$, $\lambda$ and a finite dyadic center grid. There are a deterministic program and polynomials $p,q$ such that, for $d\le\Delta$, a center tuple $c$ on the grid, total degree $K$ and precision $L$, the program encloses all coefficients of $F_d(c+z)$ and $P_d(c+z)$ through degree $K$ in certified intervals of width at most $2^{-L}$, in time at most $q(K+L)$, with working precision
--
--   $$
--   W=L+p\bigl(K+\lceil\log_2(L+2)\rceil\bigr).
--   $$
--
--   This is not a claim about arbitrary computable analytic functions; the fixed dimension and fixed grid matter. The polynomial $p$ may depend on the grid.
--
--   Differences from the source:
--   - encoding: an algorithm in the informally described word and bit cost model → a finite program of the Machine language; reason: a concrete instruction set of that model; every such program is an algorithm in the source's model, and restricting address arithmetic to increment, decrement and paid conversion only charges more than the source does
--   - generalization: the fixed dyadic grid of Lemma 9 → any finite dyadic grid of nonnegative centers; reason: the proof uses only that the centers form a finite set of nonnegative dyadics; Lemma 9's grid is one
--   - encoding: working precision L + p(K + log(L+2)) → every number register and number-memory cell throughout the run has at most W bits, for W = L + p(K + ⌈log₂(L+2)⌉); reason: the precision bound applies also to intermediate whole-number operands; products may be evaluated in digits, and changing the logarithm base or taking a ceiling is absorbed into p
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Lemma 16, printed p.13 (PDF p.14)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Specs

namespace HardCoreLocalSampling.Local

/-- Thomas Chen, STOC 2027 submission #462, Lemma 16, printed p.13 (PDF p.14).
For a fixed dyadic center grid, one program takes `d`, grid indices, `K` and `L`, and encloses all
coefficients of `F_d(c+z)` and `P_d(c+z)` through degree `K` in intervals of width at most `2^{-L}`,
in time polynomial in `K + L`, with working precision `W = L + p(K + ⌈log₂(L+2)⌉)`: no number in the
run exceeds `W` bits. Long products can be computed in digits within this bound. The output cells are fixed by
`gradedIndices`. -/
theorem effective_taylor_coefficients (Delta : ℕ) (lam : ℚ) (hS : Standing Delta lam)
    (k J : ℕ) :
    ∃ (P : Program) (p q : Polynomial ℕ),
      ∀ (d : ℕ), d ≤ Delta → ∀ j : Fin d → ℕ, (∀ i, j i ≤ J) →
        let c : Fin d → ℝ := fun i => (j i : ℝ) / 2 ^ k
        ∀ (K L : ℕ) (ω : ℕ → Bool),
          let init : Config := { N := regsOf [d, K, L], Nm := regsOf (List.ofFn j) }
          let W : ℕ := L + p.eval (K + Nat.clog 2 (L + 2))
          let idx := gradedIndices d K
          NumbersFit P noOracle ω noExt init W ∧
          RunsTo P noOracle ω noExt init (q.eval (K + L)) 0 fun cfg =>
            ∀ n (hn : n < idx.length),
              EnclosesAt cfg (6 * n) L (taylorCoeff (Fd (lam : ℝ)) c idx[n]) ∧
              EnclosesAt cfg (6 * (idx.length + n)) L (taylorCoeff (Pd (lam : ℝ)) c idx[n]) := by sorry

end HardCoreLocalSampling.Local
