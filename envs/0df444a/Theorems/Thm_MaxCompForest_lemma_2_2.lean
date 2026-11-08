-- Prove2me | Theorems.Thm_MaxCompForest_lemma_2_2
-- name    : MaxCompForest.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:37:57.335992+00:00
-- url     : https://prove2.me/theorems/f5ec12a0-cf77-4e39-af57-b8f1576e6ff0
-- title:
--   Lemma 2.2 — weighted pseudometric growth
-- statement:
--   Let $G$ be a finite loopless weighted graph on $n\ge2$ vertices, $\rho$ a finite pseudometric on the row labels and $w_v>0$. For every $T>0$ there are positive radii $r_v$ and selected row facilities $C$ such that
--   $$
--   |r_u-r_v|\le\rho(u,v),\qquad \sum_v w_v(r_v-\rho(c,v))_+^2\le T\ \text{ for every row }c,\qquad \rho(v,C)\le3r_v .
--   $$
--   Each selected facility has a tent $f_c(v)=(r_v-\rho(c,v))_+$ of $W$-norm squared exactly $T$. These tents have disjoint nonzero supports, are 2-Lipschitz, and
--   $$
--   \sum_{c\in C}\mathcal E(f_c)\le8\mathcal E_\rho .
--   $$
--   If $\lambda_{q+1}(N_W)\ge\gamma$, then for every integer $s\ge0$, $T>16\mathcal E_\rho/((s+1)\gamma)$ implies $|C|\le q+s$. The weighted assignment cost of $C$ is at most $9\sum_v w_vr_v^2$.
--
--   This is the facility construction that turns the spectral assumption into a center count.
--
--   Differences from the source:
--   - encoding: $\rho(v,C)\le3r_v$, with $C$ implicitly nonempty → `∃ c ∈ C, ρ c v ≤ 3 * r v`, and `C.Nonempty` in the witness; reason: the minimum over $C$ needs a nonempty set, which (2.5) forces
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 2.2, pp.7–8; §2.1 p.7

import Mathlib
import Definitions.Def_MaxCompForest_lam
import Definitions.Def_MaxCompForest_tent
import Definitions.Def_MaxCompForest_FinPseudo
import Definitions.Def_MaxCompForest_fnEnergy
import Definitions.Def_MaxCompForest_distEnergy
import Definitions.Def_MaxCompForest_rowCost
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

/-- **Lemma 2.2 (Weighted pseudometric growth).** Radii and facilities come before `q`, `γ`, `s`: one set `C`
serves every `s`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), pp.7–8, under the standing assumptions of §2.1, p.7 (finite loopless weighted graph on
`n ≥ 2` vertices, possibly disconnected; arbitrary positive masses).

**Formalization Note.** (2.5) is `∃ c ∈ C, ρ c v ≤ 3 r v`. "Nonzero supports" follows from tightness and `T > 0`. -/
theorem lemma_2_2 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (hn : 2 ≤ Fintype.card V) (W : V → ℝ) (hW : ∀ v, 0 < W v)
    (ρ : V → V → ℝ) (hρ : FinPseudo ρ) (T : ℝ) (hT : 0 < T) :
    ∃ (r : V → ℝ) (C : Finset V) (hC : C.Nonempty),
      (∀ v, 0 < r v) ∧
      (∀ u v, |r u - r v| ≤ ρ u v) ∧
      (∀ c, ∑ v, W v * tent r ρ c v ^ 2 ≤ T) ∧
      (∀ v, ∃ c ∈ C, ρ c v ≤ 3 * r v) ∧
      (∀ c ∈ C, ∑ v, W v * tent r ρ c v ^ 2 = T) ∧
      (∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → ∀ v, tent r ρ c v = 0 ∨ tent r ρ c' v = 0) ∧
      (∀ c ∈ C, ∀ u v, |tent r ρ c u - tent r ρ c v| ≤ 2 * ρ u v) ∧
      ∑ c ∈ C, fnEnergy G (tent r ρ c) ≤ 8 * distEnergy G ρ ∧
      (∀ (q : ℕ) (γ : ℝ) (s : ℕ), 1 ≤ q → q < Fintype.card V → 0 < γ → γ ≤ lam G W q →
        16 * distEnergy G ρ / (((s : ℝ) + 1) * γ) < T → C.card ≤ q + s) ∧
      rowCost W ρ C hC ≤ 9 * ∑ v, W v * r v ^ 2 := by sorry

end MaxCompForest
