-- Prove2me | Theorems.Thm_LogConcaveLattice_Lift_Supplement_theorem_1_7
-- name    : LogConcaveLattice.Lift.Supplement.theorem_1_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:36:16.316955+00:00
-- url     : https://prove2.me/theorems/2cdd7f1b-e6ef-4a2f-88ed-8a8534e34204
-- title:
--   Theorem 1.7 — reverse Minkowski: $\rho_s(\Lambda)\le 3/2$ for weakly stable $\Lambda$ and $0<s\le1/\sqrt{2e\log(3n)}$
-- statement:
--   Let $\Lambda\subseteq\mathbb R^n$ be a full-rank weakly stable lattice: every sublattice $\Gamma\subseteq\Lambda$ (of any rank) has $\det\Gamma\ge1$. For $s>0$ let $\rho_s(x)=e^{-\pi\|x\|_2^2/s^2}$. Then for every $s$ with
--
--   $$0<s\le\frac1{\sqrt{2e\,\log(3n)}}$$
--
--   the Gaussian mass of $\Lambda$ converges and
--
--   $$\rho_s(\Lambda)=\sum_{\lambda\in\Lambda}\rho_s(\lambda)\ \le\ \frac32 .$$
--
--   The paper prints the threshold as $\big(\tfrac1{\sqrt{2e}}+o(1)\big)\tfrac1{\sqrt{\log n}}$; the proof on p. 20 establishes it in the explicit form above, which is the printed form with $o(1)=\varepsilon(n):=\tfrac1{\sqrt{2e}}\big(\sqrt{\log n/\log(3n)}-1\big)\to0$. The dependence $1/\sqrt{\log n}$ is sharp ($\Lambda=\mathbb Z^n$). This is a new proof of the reverse Minkowski theorem of Regev and Stephens-Davidowitz with an explicit constant.
--
--   **Formalization Note** $\rho_s$ and $\rho_s(\Lambda)$ are the mission's published `rhoScalar` and `rhoScalarMass` (a `tsum`); summability is part of the conclusion, so the bound cannot hold through the junk value $0$ of a divergent sum. The theorem says "weakly stable lattice"; by the convention of §2.3 (p. 7) it is full rank, as in Corollary 4.4 which its proof uses. Logarithms are natural (§2.1). For $n=0$ Lean evaluates $\log 0=0$ and $1/\sqrt0=0$, so no $s>0$ qualifies and the statement is vacuous there (and $\rho_s(\{0\})=1$ anyway).
--
--   Differences from the source:
--   - generalization: for all 0 < s ≤ (1/√(2e) + o(1)) · 1/√(log n) → for every n and all 0 < s ≤ 1/√(2e · log(3n)); reason: the explicit threshold proved on p. 20; it is the printed threshold with o(1) := (1/√(2e))(√(log n / log(3n)) − 1) → 0, so it implies the printed statement
--   - encoding: ∑_{λ∈Λ} ρ_s(λ) ≤ 3/2 → Summable (λ ↦ rhoScalar s λ) and rhoScalarMass s Λ ≤ 3/2; reason: the summability clause guards against the tsum junk value 0; a sum of positive terms bounded by 3/2 converges, so no instance changes
--   - reading: Λ ⊆ ℝⁿ a weakly stable lattice → Λ a full-rank weakly stable lattice ([DiscreteTopology Λ] [IsZLattice ℝ Λ]); reason: §2.3 (p. 7) assumes full rank unless stated otherwise, and the proof (p. 20) goes through Corollary 4.4, stated for full rank; no instance is lost, since a rank-k weakly stable Λ is a full-rank weakly stable lattice of its span ≅ ℝᵏ (determinants are intrinsic) and 1/√(2e·log(3n)) ≤ 1/√(2e·log(3k))
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, SHA-256 c2ca89e66a6221772830cc9470a9d1f7fb2afeb8fc716a1b283f35b2280c5eac, Theorem 1.7, p. 5; explicit threshold s ≤ 1/√(2e log(3n)) in the proof of Theorem 1.7, p. 20 (via Corollary 4.4 (4.6), p. 19); ρ_s p. 6; weak stability p. 2; full rank by default §2.3 p. 7; natural logarithms §2.1 p. 5

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice
import Definitions.Def_LogConcaveLattice_Lift_Gaussian

namespace LogConcaveLattice.Lift.Supplement

/-- **Theorem 1.7** (reverse Minkowski; Letwin–Reis–Rothvoss, p. 5, proof p. 20). Let
`Λ ⊆ ℝⁿ` be a full-rank weakly stable lattice. Then for every `0 < s ≤ 1/√(2e · log(3n))`,
`ρ_s(Λ) = ∑_{λ∈Λ} e^{-π‖λ‖²/s²}` converges and is at most `3/2`. The explicit threshold is the
one the proof on p. 20 establishes; it is the printed `(1/√(2e) + o(1)) · 1/√(log n)` with the
`o(1)` term `(1/√(2e)) (√(log n / log(3n)) − 1) → 0`. For `n = 0` the threshold is `0` in Lean
and the statement is vacuous (and `ρ_s({0}) = 1` anyway). -/
theorem theorem_1_7 (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛ : WeaklyStable Λ) (s : ℝ) (hs : 0 < s)
    (hsle : s ≤ 1 / Real.sqrt (2 * Real.exp 1 * Real.log (3 * (n : ℝ)))) :
    Summable (fun l : Λ => rhoScalar s (l : V n)) ∧ rhoScalarMass s Λ ≤ 3 / 2 := by sorry

end LogConcaveLattice.Lift.Supplement
