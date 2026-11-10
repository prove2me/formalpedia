-- Prove2me | Theorems.Thm_OptRobustCD_theorem_4_2
-- name    : OptRobustCD.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T00:27:50.968615+00:00
-- url     : https://prove2.me/theorems/b32697cc-d8a0-4a14-ba66-98224e6cb6fe
-- title:
--   Theorem 4.2 — BP from the second nonbacktracking eigenvector is optimal, robustly, in $O_{d,\lambda,\varepsilon}(n)$ operations
-- statement:
--   Let $d>0$, $\lambda\in(-1,1)$ with $d\lambda^2>1$, let $(G,\sigma^\star)\sim\mathrm{SBM}(n,d,\lambda)$, and let $\xi$ be a unit eigenvector of $B_G$ for its eigenvalue of second-largest modulus. For every $\varepsilon>0$ there are $t\ge1$, $\gamma\in(0,1)$, $\beta>0$ and $\eta>0$ such that the following holds with high probability. For every graph $G'$ on $[n]$ with $|E(G)\triangle E(G')|\le\eta n$ and every unit $y\in\mathbb R^{\vec E(G')}$ with $\langle y,\xi\rangle^2\ge1-\eta$, the output $\hat\sigma$ of $\mathrm{BP}_{t,\gamma}(G',\beta\sqrt{|\vec E(G')|}\,y)$ satisfies
--   $$\mathbb E\,\mathrm{ov}(\hat\sigma,\sigma^\star)\ge\mathrm{OPT}_{d,\lambda}-\varepsilon,$$
--   the expectation over the random rounding, and the procedure uses $O_{d,\lambda,\varepsilon}(n)$ arithmetic operations. $\mathrm{OPT}_{d,\lambda}$ is the tree quantity of §3.3.
--
--   The case $\eta$ small and $G'=G$ answers Zdeborová's question: BP initialized at the second nonbacktracking eigenvector is optimal. This is the first half of the main theorem.
--
--   Differences from the source:
--   - encoding: OPT_{d,λ} = lim_t E|M_t| → treeOPT = inf_t E|M_t|; reason: E|M_t| is nonincreasing (p.14), so the limit is the infimum
--   - reading: let ξ be a unit eigenvector for the eigenvalue of B_G of second-largest modulus → inside the event: such a ξ (IsInfEig) exists, and the conclusion holds for every such ξ; reason: the paper presumes the eigenvalue real and simple, which holds w.h.p.; the existence clause rules out vacuity
--   - encoding: with high probability → the SBM(n,d,λ) probability of the event tends to 1 (Whp); reason: the meaning of the phrase
--   - reading: the procedure uses O_{d,λ,ε}(n) arithmetic operations → one real-RAM program P (no oracle) and one C, chosen before n, such that on the event, for every admissible G′, y and every encoding of (G′, Y), P halts within C·n steps on every tape, outputs a ±1 labelling, and its output law under the tape measure is the law of BP_{t,γ}(G′, Y); reason: the paper names no machine; OptRobustCD.Machine has the operations BP uses (arithmetic, tanh, uniform draws)
--   - encoding: τ_e drawn for each directed edge e → τ drawn for every ordered pair with weight ∏(1+τ_p tanh Y_p)/2; reason: the output depends only on directed edges, so its law is unchanged
--   - reading: sign(BP(·)) with no rule at 0 → sign(0) = +1; reason: BP(∅) = 0 at isolated vertices; the paper fixes no rule and the argument does not depend on it
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Theorem 4.2, p.16 (pdf p.18)

import Mathlib
import Definitions.Def_OptRobustCD_Whp
import Definitions.Def_OptRobustCD_BP
import Definitions.Def_OptRobustCD_NBMatrix
import Definitions.Def_OptRobustCD_treeOPT
import Definitions.Def_OptRobustCD_Layouts

open MeasureTheory

namespace OptRobustCD

/-- **Theorem 4.2** (BP from the second eigenvector is optimal, robustly). Hopkins, Hua, Mohanty,
Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027 submission (manuscript of
November 3, 2026, sha256 3d287d54…), Theorem 4.2, p.16 (pdf p.18).

"Let dλ² > 1 and (G, σ⋆) ∼ SBM(n, d, λ), and let ξ be a unit eigenvector for the eigenvalue of `B_G`
of second-largest modulus. For every ε > 0 there are t ⩾ 1, γ ∈ (0, 1), β > 0, and η > 0 such that
the following holds with high probability. For every graph G′ on [n] with |E(G)△E(G′)| ⩽ ηn and
every unit `y ∈ R^{E⃗(G′)}` such that `⟨y, ξ⟩² ⩾ 1 − η`, the output σ̂ of
`BP_{t,γ}(G′, β√|E⃗(G′)| y)` satisfies `E ov(σ̂, σ⋆) ⩾ OPT_{d,λ} − ε`, where the expectation is over
the random rounding in `BP_{t,γ}`, and the procedure uses `O_{d,λ,ε}(n)` arithmetic operations."

**Formalization Note.**
* `OPT_{d,λ}` is the tree quantity of §3.3 (`treeOPT`). `β` is existential, as printed.
* The event asserts that an informative eigenvector `ξ` exists (`IsInfEig`) and then quantifies
  over all of them, then over `G′` and `y`.
* Operation count: one program `P` of the real RAM (`Machine`, with `tanh` and uniform draws, no
  oracle) and one constant `C`, both chosen after `d, λ, ε` and before `n`, such that on the event,
  for every admissible `G′, y` and every encoding of `(G′, Y)`, `Y = β√|E⃗(G′)| y`, `P` halts within
  `C·n` steps on every tape, outputs a `±1` labelling, and its output law under the tape measure is
  the law of `BP_{t,γ}(G′, Y)`.
* `d > 0`, `λ ∈ (−1, 1)` are the standing assumptions of §3.1 (p.12). -/
theorem theorem_4_2 (d lam : ℝ) (hd : 0 < d) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1)
    (hKS : 1 < d * lam ^ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℕ, 1 ≤ t ∧ ∃ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ β : ℝ, 0 < β ∧ ∃ η : ℝ, 0 < η ∧
    ∃ C : ℝ, ∃ P : Program, NoOracle P ∧ Whp d lam (fun n σ G =>
      (∃ ξ : EVec n, IsInfEig G ξ) ∧ ∀ ξ : EVec n, IsInfEig G ξ →
      ∀ G' : SimpleGraph (Fin n), (editDist G G' : ℝ) ≤ η * n →
      ∀ y : EVec n, SupportedOn G' y → l2 y = 1 → 1 - η ≤ ip y ξ ^ 2 →
        treeOPT d lam - ε ≤
            bpExpOv G' lam t γ (fun p => β * Real.sqrt (numArcs G') * y p) σ ∧
        ∀ l : List ℝ, GraphValCode G' (fun p => β * Real.sqrt (numArcs G') * y p) l →
          HaltsWithin P noOracle l (C * n) ∧ (∀ ω, IsLabelling n (finalOut P noOracle l ω)) ∧
          ∀ x : Fin n → Bool,
            tapeMeasure {ω | labelOfList n (finalOut P noOracle l ω) = x} =
              ENNReal.ofReal
                (bpProb G' lam t γ (fun p => β * Real.sqrt (numArcs G') * y p) x)) := by sorry

end OptRobustCD
