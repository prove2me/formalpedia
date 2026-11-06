-- Prove2me | Theorems.Thm_MatrixLewis_lemma_3_19
-- name    : MatrixLewis.lemma_3_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:06:13.168202+00:00
-- url     : https://prove2.me/theorems/5f515051-84ed-491b-8ca6-2d9c2bb874b2
-- title:
--   Lemma 3.19 — power traces along congruence curves
-- statement:
--   Let $q>2$, and let $G$ and $F$ be real symmetric matrices of the same size. Put $G_t=e^{tF/2}Ge^{tF/2}$ and
--   $$
--   \chi(t)=\operatorname{tr}|G_t|^q,\qquad |Y|=(Y^2)^{1/2}.
--   $$
--   Then $\chi$ is three times continuously differentiable, and there is an absolute constant $C_{\mathrm{pt}}$ such that
--   $$
--   |\chi'''(0)|\le C_{\mathrm{pt}}\,q\,\|F\|_{\mathrm{op}}\bigl(\chi''(0)+q\operatorname{tr}(|G|^qF^2)\bigr).
--   $$
--
--   If $F$ and $G$ commute the bound holds without the energy term; the lemma shows that noncommutativity costs only an absolute constant and the extra term $q\operatorname{tr}(|G|^qF^2)$. It is independent of the barrier.
--
--   **Formalization Note** $\|\cdot\|_{\mathrm{op}}$ is the published `LiqPremiaEq.opNorm` (the $\ell^2$ operator norm). $C_{\mathrm{pt}}$ is chosen before the size, $G$, $F$ and $q$; the size is any finite index type.
--
--   Differences from the source:
--   - encoding: |Y|^q with |Y| = (Y²)^{1/2}; e^{tF/2} → functional calculus of s ↦ |s|^q and s ↦ e^s; reason: for symmetric matrices these agree with the paper's matrix functions
--   - encoding: real symmetric matrices of the same size → Matrix ι ι ℝ for any finite index type ι in Type; reason: every finite index type is in bijection with Fin n
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.19, p.29

import Mathlib
import Definitions.Def_MatrixLewis_mpow
import Definitions.Def_LiqPremiaEq_opNorm

namespace MatrixLewis

/-- **Lemma 3.19** (Power traces along congruence curves; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), p.29). Let `q > 2`, and let
`G` and `F` be real symmetric matrices of the same size. Put `G_t = e^{tF/2}Ge^{tF/2}` and
`χ(t) = tr |G_t|^q`, where `|Y| = (Y²)^{1/2}`. Then `χ` is three times continuously
differentiable, and for an absolute constant `C_pt`,
`|χ‴(0)| ≤ C_pt q ‖F‖_op (χ″(0) + q tr(|G|^q F²))`.

**Formalization Note** `‖·‖_op` is the published `LiqPremiaEq.opNorm` (the ℓ² operator norm of a real matrix). `C_pt` is quantified before the size, `G`, `F` and `q`. The size is any
finite index type `ι`. `e^{tF/2}` is `mexp ((t/2) • F)` and `|Y|^q` is `mabsPow q Y`
(functional calculus). -/
theorem lemma_3_19 :
    ∃ Cpt : ℝ, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G F : Matrix ι ι ℝ) (q : ℝ),
      2 < q → G.IsHermitian → F.IsHermitian →
      let χ : ℝ → ℝ := fun t =>
        (mabsPow q (mexp ((t / 2) • F) * G * mexp ((t / 2) • F))).trace
      ContDiff ℝ 3 χ ∧
        |iteratedDeriv 3 χ 0| ≤
          Cpt * q * LiqPremiaEq.opNorm F * (iteratedDeriv 2 χ 0 + q * (mabsPow q G * F ^ 2).trace) := by sorry

end MatrixLewis
