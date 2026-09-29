-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_continuous_and_isGaugeMajorised3_of_eq_mul_prod
-- name    : LanglandsTunnell.CubicInduction.continuous_and_isGaugeMajorised3_of_eq_mul_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/9d71405f-9c55-5834-a76e-00f8b8491886
-- title:
--   Continuity and gauge majorisation of factorisable functions on adelic GL₃
-- statement:
--   Fix a function $W_\infty$ on $\mathrm{GL}_3$ of the infinite adeles of $\mathbb{Q}$ with values in $\mathbb{C}$, for each finite place $v$ of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$) a function $W_v$ on $\mathrm{GL}_3(\mathbb{Q}_v)$, a finite set $S$ of finite places, and a function $W$ on $\mathrm{GL}_3$ of the adele ring of $\mathbb{Q}$. Assume: (`hfac`) for every adelic $g$ and every finite $T \supseteq S$ such that the component of $g$ at each $v \notin T$ lies in the subgroup of matrices all of whose entries and all of whose inverse's entries have valuation $\le 1$, one has $W(g) = W_\infty(g_\infty) \prod_{v \in T} W_v(g_v)$; (`hinv`) for $v \notin S$, $W_v(g u) = W_v(g)$ for $g \in \mathrm{GL}_3(\mathbb{Q}_v)$ and $u$ in that same subgroup; (`hsph`) there is a single $t \in \mathbb{N}$ such that for all $v \notin S$ and all $h$, writing $a(h) = \mathrm{detSize}(h)\cdot\mathrm{lastRowSup}(h)/\mathrm{minorSup}(h)^2$ and $b(h) = \mathrm{minorSup}(h)/\mathrm{lastRowSup}(h)^2$, $W_v(h) = 0$ unless $a(h) \le 1$ and $b(h) \le 1$, while in that case $\|W_v(h)\| \le 1/(a(h)b(h))^t$; (`hS`) for each $v \in S$ there is an open subgroup $U_v$ of $\mathrm{GL}_3(\mathbb{Q}_v)$ with $W_v(gk) = W_v(g)$ for all $k \in U_v$ and all $g$, and there are $B, C \in \mathbb{R}$ and $t \in \mathbb{N}$ with $W_v(h) = 0$ unless $a(h) \le B$ and $b(h) \le B$, and $\|W_v(h)\| \le C/(a(h)b(h))^t$ in that case; (`harch`) $W_\infty$ is continuous and there is $t \in \mathbb{N}$ such that for every $N \in \mathbb{N}$ there is $C \in \mathbb{R}$ with $\|W_\infty(g_\infty)\| \le C/\big((\prod_{w} \mathrm{archRoot}_1(w,g)\,\mathrm{archRoot}_2(w,g))^t (1 + \mathrm{archRootSum}(g))^N\big)$ for all adelic $g$, the product being over the infinite places of $\mathbb{Q}$. Here $\mathrm{lastRowSup}$, $\mathrm{minorSup}$, $\mathrm{detSize}$ are the maximum of the norms of the last-row entries, the maximum of the norms of the three $2\times 2$ minors of the last two rows, and the norm of the determinant. The conclusion is that $W$ is continuous and is gauge-majorised: there exist $t \in \mathbb{N}$, a finite set $T$ of finite places and $B \in \mathbb{R}$ such that for every $N \in \mathbb{N}$ there is $C \in \mathbb{R}$ with, for all $g$, $W(g) = 0$ unless $g$ lies in root level $(T,B)$ (i.e. $\mathrm{finRoot}_1, \mathrm{finRoot}_2 \le 1$ at all $v \notin T$ and $\le B$ at all $v \in T$), and $\|W(g)\| \le C/(\mathrm{rootSizeProd}(g)^t (1 + \mathrm{archRootSum}(g))^N)$ when it does, where $\mathrm{rootSizeProd}$ is the product of the finite-place factors $\mathrm{finRoot}_1\,\mathrm{finRoot}_2$ over all finite places times the product of $\mathrm{archRoot}_1\,\mathrm{archRoot}_2$ over the infinite places.
--
--   This is the assembly step of the cubic-induction apparatus: it converts local data (spherical bounds and right invariance away from $S$, open invariance and threshold bounds at $S$, and a rapidly decreasing archimedean factor) into the two global properties — continuity and the gauge majorant with prescribed root level — required of a global Whittaker-type function on $\mathrm{GL}_3$ of the adeles of $\mathbb{Q}$. It is used in the construction of cubic induction data with prescribed archimedean behaviour, torus values and local package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_continuous_and_isGaugeMajorised3_of_eq_mul_prod.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.continuous_and_isGaugeMajorised3_of_eq_mul_prod
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hfac : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W g = Warch (archComponent3 (𝓞 ℚ) ℚ g) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v g))
    (hinv : ∀ v, v ∉ S → IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (Wloc v))
    (hsph : ∃ t : ℕ, ∀ v, v ∉ S → ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1) → Wloc v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1 →
        ‖Wloc v h‖ ≤ 1 / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (hS : ∀ v ∈ S,
      (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, Wloc v (g * k) = Wloc v g) ∧
      ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
          (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → Wloc v h = 0) ∧
          (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
            ‖Wloc v h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (harch : Continuous Warch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) :
    Continuous W ∧ IsGaugeMajorised3 ℚ W := by sorry
