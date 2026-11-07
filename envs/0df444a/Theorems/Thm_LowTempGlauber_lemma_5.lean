-- Prove2me | Theorems.Thm_LowTempGlauber_lemma_5
-- name    : LowTempGlauber.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:48.742859+00:00
-- url     : https://prove2.me/theorems/fedfc004-a753-4a6d-b2a6-cfa74f11ccdb
-- title:
--   Lemma 5 — a weak Poincaré inequality on the hypercube $\{-1,1\}^k$
-- statement:
--   Let $\nu$ be the uniform distribution on $\{-1,1\}^k$ and let $B\subseteq\{-1,1\}^k$. For $\sigma\in\{-1,1\}^k$ let $\sigma^{(i)}$ be the configuration obtained by flipping coordinate $i$. Then every function $g:\{-1,1\}^k\to\mathbb R$ satisfies
--   $$\operatorname{Var}_\nu(g)\le\frac14\,\mathbb E_{\sigma\sim\nu}\Bigl[\mathbf 1\{\sigma\notin B\}\sum_{i=1}^k\bigl(g(\sigma)-g(\sigma^{(i)})\bigr)^2\Bigr]+\frac{k\,\nu(B)}4\,(g_{\max}-g_{\min})^2.$$
--
--   This is the hypercube inequality used, after orienting the disagreement components of a pair of independent sets, in the one-component reduction (6) of the proof of Lemma 7.
--
--   Differences from the source:
--   - encoding: {−1, 1}^k → Fin k → Bool, with ν(σ) = 2^{−k} and ν(B) = |B|/2^k; reason: a relabelling of the two coordinate values; same instances
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Lemma 5, p.8

import Mathlib
import Definitions.Def_LowTempGlauber_ChainLayer

namespace LowTempGlauber

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…), Lemma 5, p.8.

Let `ν` be the uniform distribution on `{−1, 1}^k` and `B ⊆ {−1, 1}^k`; `σ^{(i)}` flips coordinate `i`.
Every `g` satisfies
`Var_ν(g) ≤ ¼ E_{σ∼ν}[1{σ ∉ B} Σ_{i=1}^k (g(σ) − g(σ^{(i)}))²] + (k ν(B)/4)(g_max − g_min)²`.

**Formalization Note.** `{−1, 1}^k` is `Fin k → Bool`; `σ^{(i)}` is `Function.update σ i (!σ i)`;
`ν(σ) = 1/2^k` and `ν(B) = |B|/2^k`. -/
theorem lemma_5 (k : ℕ) (B : Finset (Fin k → Bool)) (g : (Fin k → Bool) → ℝ) :
    variance (fun _ => (1 : ℝ) / 2 ^ k) g ≤
      (1 / 4) * ∑ σ : Fin k → Bool, (1 / 2 ^ k : ℝ) *
          (if σ ∉ B then ∑ i : Fin k, (g σ - g (Function.update σ i (!σ i))) ^ 2 else 0) +
        (k : ℝ) * ((B.card : ℝ) / 2 ^ k) / 4 * osc g ^ 2 := by sorry

end LowTempGlauber
