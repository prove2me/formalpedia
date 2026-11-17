-- Prove2me | Theorems.Thm_MonoTestDAG_Supplement_theorem_4_8
-- name    : MonoTestDAG.Supplement.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:49:18.448204+00:00
-- url     : https://prove2.me/theorems/91cac528-f1e7-4b3b-84e0-d07dade526c5
-- title:
--   Theorem 4.8 — the explicit graph has $s=\Omega(n_0^{k/(k+2)})$ positive matchings
-- statement:
--   Fix $\varepsilon\in(0,1/2]$ and an integer $k\ge2$. There is a choice $\alpha=\alpha(\varepsilon,k)\in(0,1)$ such that, for all sufficiently large $N$ with $P=\lfloor\alpha N\rfloor\ge1$, the explicit box-and-shift graph $U(N,k,\alpha)$ is an $(s,\varepsilon)$-PMRS graph with
--
--   $$
--   n_0=N^{k+2},\qquad s=(P+1)^k-1=\Omega\!\left(n_0^{k/(k+2)}\right).
--   $$
--
--   In particular, for $k=2$ this construction has $s=\Omega(\sqrt{n_0})$ pairwise edge-disjoint positive matchings of linear size.
--
--   This supplies the explicit combinatorial family used in the near-$\sqrt{n/\varepsilon}$ lower bound.
--
--   **Formalization Note.** `ExplicitVertex N k` is the zero-based copy of $[N]^k\times[N^2]$, and `explicitPMRSGraph` includes precisely the translations that remain inside the box.
--
--   Differences from the source:
--   - encoding: $[N]=\{1,\ldots,N\}$ and in-box translations → `Fin N` coordinates and the same translations after subtracting one from every coordinate; reason: the relabeling is a graph isomorphism and changes no instance
--   - encoding: “for all sufficiently large $N$” and $s=\Omega(n_0^{k/(k+2)})$ → a threshold $N_0$ and a positive constant $C$ chosen after $(\varepsilon,k)$, with the bound required for every $N\ge N_0$; reason: this is the quantified meaning of the asymptotic statement
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Theorem 4.8, p.21 (PDF 23), proof p.22 (PDF 24)

import Mathlib
import Definitions.Def_MonoTestDAG_IsPMRSWitness
import Definitions.Def_MonoTestDAG_Supplement_explicitPMRSGraph

namespace MonoTestDAG.Supplement

/-- **Theorem 4.8 (PMRS graphs with polynomially many matchings).** For `ε ∈ (0,1/2]`
and an integer `k ≥ 2`, one can choose `α=α(ε,k) ∈ (0,1)` so that, for all sufficiently
large `N` with `P=⌊αN⌋≥1`, the explicit graph `U(N,k,α)` is an `(s,ε)`-PMRS graph,
where `n₀=N^(k+2)`, `s=(P+1)^k-1`, and `s=Ω(n₀^(k/(k+2)))`. For `k=2`, this gives
`s=Ω(√n₀)`.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Theorem 4.8, pp.21–22.

**Formalization Note.** `ExplicitVertex N k` is `[N]^k×[N²]`, and `explicitPMRSGraph` is
exactly the union of the in-box translations by nonzero shifts in `{0,…,P}^k`. The positive
constant `C` and threshold `N₀` may depend on `ε,k`, as does `α`. -/
theorem theorem_4_8 :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ k : ℕ, 2 ≤ k →
      ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        1 ≤ explicitP N α ∧
        Fintype.card (ExplicitVertex N k) = N ^ (k + 2) ∧
        explicitS N k α = (explicitP N α + 1) ^ k - 1 ∧
        IsPMRSGraph (explicitPMRSGraph N k α) ε (explicitS N k α) ∧
        C * (Fintype.card (ExplicitVertex N k) : ℝ) ^ ((k : ℝ) / (k + 2 : ℕ)) ≤
          (explicitS N k α : ℝ) ∧
        (k = 2 → C * Real.sqrt (Fintype.card (ExplicitVertex N k) : ℝ) ≤
          (explicitS N k α : ℝ)) := by sorry

end MonoTestDAG.Supplement
