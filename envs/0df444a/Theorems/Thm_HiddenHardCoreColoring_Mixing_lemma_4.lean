-- Prove2me | Theorems.Thm_HiddenHardCoreColoring_Mixing_lemma_4
-- name    : HiddenHardCoreColoring.Mixing.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:00:34.792828+00:00
-- url     : https://prove2.me/theorems/cd38b1b9-85d2-4c7f-a55a-ea5d8f128031
-- title:
--   Lemma 4 — gap(P) ≥ κ/n if and only if ‖Lf‖² ≥ κ⟨f, Lf⟩ for all f
-- statement:
--   Throughout, $G=(V,E)$ is a finite simple graph on $n=|V|\ge1$ vertices with $\deg(v)\le\Delta$ for every $v$, $[q]=\{0,\dots,q-1\}$ is the palette, $\Omega$ is the set of proper $q$-colorings, $\mu$ is uniform on $\Omega$, and $q\ge\Delta+3$ (the standing assumption of §§3.2–7). Let $P$ be the heat-bath Glauber dynamics on $\Omega$ (pick a uniform vertex $v$, recolor it with a uniform color of $A_v(\sigma)$) and $L=\sum_vQ_v=n(\mathrm{Id}-P)$. For every $\kappa>0$,
--   $$\operatorname{gap}(P)\ge\frac\kappa n\iff\|Lf\|_\mu^2\ge\kappa\langle f,Lf\rangle_\mu\quad\text{for every }f\in L^2(\mu).$$
--
--   This integrated Bochner criterion is how the spectral gap in Theorem 1 is certified.
--
--   **Formalization Note** $P$ is the published `MarkovMixing.coloringGlauber G q` on the subtype of proper colorings; $L$ is the mission's sum of $Q_v=\mathrm{Id}-P_v$.
--
--   Differences from the source:
--   - encoding: eigenvalues of the reversible chain listed with multiplicity, gap(P) = 1 − λ₂(P) → gap P = 1 − λ₂ with λ₂ := 1 if the eigenspace of 1 has dimension ≥ 2 and otherwise the largest real eigenvalue ≠ 1; reason: for a chain reversible with respect to a full-support law all eigenvalues are real and at most 1, so this is the second eigenvalue counted with multiplicity
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; Lemma 4, p.7; standing assumptions of §3.2, p.7

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Coloring

open Finset Matrix

namespace HiddenHardCoreColoring.Mixing

/-- **Lemma 4** (Xiongxin Yang, STOC 2027 submission #964 (October 2026), p.7). Under the standing assumptions of §3.2 (`deg(v) ≤ Δ`, `q ≥ Δ + 3`),
for every `κ > 0`: `gap(P) ≥ κ/n` if and only if `‖Lf‖²_µ ≥ κ⟨f, Lf⟩_µ` for every `f ∈ L²(µ)`, where
`P` is the Glauber dynamics on proper `q`-colorings and `L = ∑_v Q_v`. -/
theorem lemma_4 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ q : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (hq : Δ + 3 ≤ q) (κ : ℝ) (hκ : 0 < κ) :
    κ / (Fintype.card V : ℝ) ≤ gap (MarkovMixing.coloringGlauber G q) ↔
      ∀ f : Col G q → ℝ, κ * ip G q f (Lap G q *ᵥ f) ≤ sqNorm G q (Lap G q *ᵥ f) := by sorry

end HiddenHardCoreColoring.Mixing
