-- Prove2me | Theorems.Thm_KTCenter_lemma_4_1
-- name    : KTCenter.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:21.795106+00:00
-- url     : https://prove2.me/theorems/15ac3e74-4ed3-4244-b088-93505128ba42
-- title:
--   Lemma 4.1 — a near-optimal ranking within the movement allowances
-- statement:
--   Relabel so that $\rho=\pi_1=(1,\dots,d)$. For every real $\delta>0$ there exist an index set $J\subseteq[n]$ with $1\in J$ and $|J|\le r=1+\lceil1/\delta\rceil$, and a complete ranking $\tau$, such that
--
--   $$\mathrm{Obj}(\Pi,\tau)\le(1+2\delta)R^*,\qquad|\mathrm{pos}_\tau(v)-v|\le w_v\quad(v\in V),\qquad(9)$$
--
--   with $w_v=5\deg_{E_J}(v)$.
--
--   This is the structural result of Section 4: the enumerated allowances contain a near-optimal center.
--
--   Differences from the source:
--
--   - encoding: candidates relabeled by their position in the first input, so ρ = π₁ = (1, …, d) (§4.1) → hypothesis `I.π I.first = 1` on the input list; reason: the relabeling preserves all distances and is undone at the end (p.17); the statements of §§4–5 are about relabeled inputs
--   - encoding: positions and labels 1, …, d → 0-based Fin d shifted by lab v = v + 1, difference in ℤ; reason: Lean convention; same values
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Lemma 4.1, eq. (9), p.16 (PDF p.18)

import Mathlib
import Definitions.Def_KTCenter_Instance
import Definitions.Def_KTCenter_InversionUnion

namespace KTCenter

/-- **Lemma 4.1**, eq. (9), p.16 (PDF p.18).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** On relabeled inputs, `π₁ = 1` (§4.1). The position `pos_τ(v) = τ⁻¹ v` and the
label `v` are on the same 1-based scale through `lab`, and the difference is in `ℤ`. `w_v` is the
allowance of the `J` found. -/
theorem lemma_4_1 (I : Instance) (hρ : I.π I.first = 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (J : Finset (Fin I.n)) (τ : Equiv.Perm (Fin I.d)),
      I.first ∈ J ∧ J.card ≤ 1 + ⌈1 / δ⌉₊ ∧
      (obj I τ : ℝ) ≤ (1 + 2 * δ) * (optRadius I : ℝ) ∧
      ∀ v : Fin I.d, |lab (τ⁻¹ v) - lab v| ≤ (allowance I J v : ℤ) := by sorry

end KTCenter
