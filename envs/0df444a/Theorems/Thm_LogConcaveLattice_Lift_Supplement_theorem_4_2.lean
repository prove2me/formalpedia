-- Prove2me | Theorems.Thm_LogConcaveLattice_Lift_Supplement_theorem_4_2
-- name    : LogConcaveLattice.Lift.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:35:50.287563+00:00
-- url     : https://prove2.me/theorems/51254e6d-7ebf-42da-95e0-f13030b9f19e
-- title:
--   Theorem 4.2 (= Theorem 1.6) — subgaussian rounding: $x=\mathbb E Y$ with $Y\in\Lambda$ and $Y-x$ $\sqrt{2e/\pi}$-subgaussian
-- statement:
--   Let $\Lambda\subseteq\mathbb R^n$ be a full-rank lattice whose dual $\Lambda^*$ is weakly stable (every sublattice of $\Lambda^*$ has determinant at least $1$), and let $x\in\mathbb R^n$. Then there is a random vector $Y$ taking values in $\Lambda$ with
--
--   1. $\mathbb E\,Y=x$, and
--   2. $Y-x$ is $s$-subgaussian with $s=\sqrt{2e/\pi}$, i.e. for every $\xi\in\mathbb R^n$
--
--   $$\mathbb E\,e^{\langle\xi,\,Y-x\rangle}\ \le\ e^{s^2\|\xi\|_2^2/2}=e^{(e/\pi)\|\xi\|_2^2}.$$
--
--   The rounding is exact in expectation and $Y$ lies in $\Lambda$ itself (not in $x+\Lambda$). The result is the subgaussian counterpart of the covering-radius bound of Theorem 1.2, connected to the vector-balancing work of Dadush, Garg, Lovett and Nikolov.
--
--   **Formalization Note** $Y$ is described by its law, a probability mass function $w:\Lambda\to[0,\infty)$ with $\sum_\lambda w(\lambda)=1$. The mean is the convergent sum $\sum_\lambda w(\lambda)\lambda=x$ (unconditional convergence in $\mathbb R^n$, i.e. absolute convergence), and for every $\xi$ the family $w(\lambda)e^{\langle\xi,\lambda-x\rangle}$ is asserted summable with sum at most $e^{(e/\pi)\|\xi\|^2}$. Theorem 4.2 says "lattice"; its introduction version, Theorem 1.6, and the convention of §2.3 make it full rank.
--
--   Differences from the source:
--   - encoding: a random vector Y ∈ Λ → a probability mass function w : Λ → ℝ with w ≥ 0 and HasSum w 1; reason: the statement only concerns the law of Y, which is a distribution on the countable set Λ; the coupling with X and Z belongs to the proof
--   - encoding: E Y = x → HasSum (fun λ => w λ • λ) x; reason: unconditional convergence in the finite-dimensional ℝⁿ is absolute convergence, i.e. existence of E Y, with value x
--   - encoding: Y − x is √(2e/π)-subgaussian: E e^{⟨ξ, Y−x⟩} ≤ e^{s²∥ξ∥²/2} → for every ξ, λ ↦ w λ · exp⟨ξ, λ − x⟩ is summable and its sum is ≤ exp((e/π)‖ξ‖²); reason: s²/2 = e/π for s = √(2e/π); the summability clause guards against the tsum junk value 0
--   - reading: Λ ⊆ ℝⁿ a lattice (Theorem 4.2, p. 17) → Λ a full-rank lattice ([DiscreteTopology Λ] [IsZLattice ℝ Λ]); reason: Theorem 1.6 (p. 5), the same result, says full-rank, and §2.3 (p. 7) assumes full rank unless stated otherwise; for a lower-rank Λ and x outside span Λ no Λ-valued Y has E Y = x, so full rank is the only reading under which the statement is meaningful
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, SHA-256 c2ca89e66a6221772830cc9470a9d1f7fb2afeb8fc716a1b283f35b2280c5eac, Theorem 4.2, p. 17 (= Theorem 1.6, p. 5); s-subgaussian p. 4; weak stability p. 2; full rank by default §2.3 p. 7

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice

open scoped RealInnerProductSpace

namespace LogConcaveLattice.Lift.Supplement

/-- **Theorem 4.2** (= Theorem 1.6; subgaussian rounding; Letwin–Reis–Rothvoss, p. 17, p. 5).
Let `Λ ⊆ ℝⁿ` be a full-rank lattice whose dual `Λ*` is weakly stable and let `x ∈ ℝⁿ`. There is
a random vector `Y ∈ Λ` with `E Y = x` such that `Y − x` is `√(2e/π)`-subgaussian, i.e.
`E e^{⟨ξ, Y − x⟩} ≤ e^{s² ‖ξ‖² / 2} = e^{(e/π) ‖ξ‖²}` for every `ξ ∈ ℝⁿ`, `s = √(2e/π)`.
The law of `Y` is a probability mass function `w` on `Λ`; the mean and the moment generating
function are (convergent) sums over `Λ`. -/
theorem theorem_4_2 (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛ : WeaklyStable (dual Λ)) (x : V n) :
    ∃ w : Λ → ℝ, (∀ l, 0 ≤ w l) ∧ HasSum w 1 ∧
      HasSum (fun l : Λ => w l • (l : V n)) x ∧
      ∀ ξ : V n, Summable (fun l : Λ => w l * Real.exp ⟪ξ, (l : V n) - x⟫) ∧
        ∑' l : Λ, w l * Real.exp ⟪ξ, (l : V n) - x⟫ ≤
          Real.exp (Real.exp 1 / Real.pi * ‖ξ‖ ^ 2) := by sorry

end LogConcaveLattice.Lift.Supplement
