-- Prove2me | Theorems.Thm_FrechetNearLinear_Main_lemma_4_5
-- name    : FrechetNearLinear.Main.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:36:46.347441+00:00
-- url     : https://prove2.me/theorems/5a6f804a-49c3-4c39-8abd-5f32304f2ceb
-- title:
--   Lemma 4.5 — Lift: R_r ⊆ Lift(B) ⊆ R_{(F+4)r}; clamping a witness gives a witness of cost (F+4)r in linear time
-- statement:
--   Let $r\ge0$ and let $B$ be an $(r,F)$-summary on the representative ports of a rectangle $R$. Then, on pairs $(s,t)$ of free input and free output points,
--   $$R_r\subseteq\mathrm{Lift}(B)\subseteq R_{(F+4)r}.$$
--   More precisely, if $s\in I_e$, $t\in I_g$ and $s\le t$, then clamping any witness $\gamma$ for $(p_e,z_g)$ (a bi-monotone path from $p_e$ to $z_g$ in $R\cap F_{Fr}$) coordinatewise to the box $[s_x,t_x]\times[s_y,t_y]$ gives a bi-monotone path from $s$ to $t$ in $R\cap F_{(F+4)r}$. The clamp is computed in time linear in the size of $\gamma$: there are an admissible program $A$ and a constant $C$ such that for every bi-monotone polygonal path with vertex list $w$ from $a$ to $b$ and every box corners $s\le t$ (input $p[0]=|w|$, memory the coordinates of $w$ then $s_x,s_y,t_x,t_y$), $A$ accepts within $C|w|$ steps and outputs a vertex list $w'$ of a bi-monotone polygonal path from $\mathrm{clamp}(a)$ to $\mathrm{clamp}(b)$ whose point set is the clamp of the point set of $w$.
--
--   The lemma extends a summary on finitely many representative ports to all free boundary points at an additive loss of $4$ in the factor.
--
--   **Formalization Note** The summary is indexed by edges; the machine is the mission's real RAM.
--
--   Differences from the source:
--   - reading: Definition 4.2's "a witness … can be reported" → the witness exists ($B\subseteq R_{Fr}$ at the representative ports); reason: the definition attaches no time bound to reporting
--   - generalization: the clamp of "a witness γ for $(p_e,z_g)$" → the clamp of every bi-monotone path from $p_e$ to $z_g$ in $R\cap F_{Fr}$, whether or not $B(p_e,z_g)$ holds; reason: every witness of the source is such a path, so it specializes
--   - generalization: the clamping-time clause for witnesses $\gamma$ and the box of $(s,t)$ → for every bi-monotone polygonal vertex list and every box $s\le t$; reason: specializes to the source's witnesses and boxes
--   - reading: "in time linear in the size of γ" → within $C|w|$ steps on the mission's real RAM with the stated input and output layout; reason: the paper names no machine; $|w|$ = segments $+1$
-- source:
--   Huang, Wang, Zhang, Constant Approximation of Fréchet Distance in Near-Linear Time, STOC 2027 submission (manuscript sha256 08be7e65…dd2d), p. 15, Lemma 4.5

import Mathlib
import Definitions.Def_FrechetNearLinear_Main_FreeSpace
import Definitions.Def_FrechetNearLinear_Main_Machine

namespace FrechetNearLinear.Main

/-- Lemma 4.5 (Lift), p. 15. Let `r ≥ 0` and let `B` be an `(r, F)`-summary on the representative
ports of `R`. (i) `R_r ⊆ Lift(B) ⊆ R_{(F+4)r}` on pairs of free input and output points.
(ii) If `s ∈ I_e`, `t ∈ I_g`, `s ≤ t`, then clamping any witness `γ` for `(p_e, z_g)` (a
bi-monotone path in `R ∩ F_{Fr}`) coordinatewise to `[s_x, t_x] × [s_y, t_y]` gives a
bi-monotone path from `s` to `t` in `R ∩ F_{(F+4)r}`. (iii) A fixed admissible program clamps a
polygonal path, given by its vertex list `w` and the box corners `s ≤ t`, within `C · |w|` steps:
its output vertex list is a bi-monotone polygonal path from `clamp(w₀)` to `clamp(w_last)` whose
point set is the clamp of the point set of `w`. -/
theorem lemma_4_5 :
    (∀ {d n m : ℕ} (P : Fin n → E d) (Q : Fin m → E d) (R : Rect n m) (r F : ℝ)
        (B : Bool × ℤ → Bool × ℤ → Prop), 0 ≤ r → IsRepSummary P Q R r F B →
        (∀ s t, s ∈ R.inB ∩ freeSpace P Q r → t ∈ R.outB ∩ freeSpace P Q r →
          (Rrel P Q R r s t → Lift P Q R r B s t) ∧
          (Lift P Q R r B s t → Rrel P Q R ((F + 4) * r) s t)) ∧
        ∀ (e g : Bool × ℤ) (s t : ℝ × ℝ), e ∈ R.inEdges → g ∈ R.outEdges →
          s ∈ freeIn P Q R r e → t ∈ freeOut P Q R r g → s ≤ t →
          ∀ γ : Path (repIn P Q R r e) (repOut P Q R r g), BiMono γ →
            (∀ u, γ u ∈ R.carrier ∩ freeSpace P Q (F * r)) →
            ∃ π : Path s t, (∀ u, π u = clampBox s t (γ u)) ∧ BiMono π ∧
              ∀ u, π u ∈ R.carrier ∩ freeSpace P Q ((F + 4) * r)) ∧
    (∃ A : Program, Admissible A ∧ ∃ C : ℝ,
      ∀ (w : List (ℝ × ℝ)) (a b s t : ℝ × ℝ), IsMonoPolyline w a b → s ≤ t →
        ∃ w' : List (ℝ × ℝ),
          ComputesListWithin A
            (initCfg [(w.length : ℤ)] (flatPts w ++ [s.1, s.2, t.1, t.2]))
            (C * (w.length : ℝ)) w' ∧
          IsMonoPolyline w' (clampBox s t a) (clampBox s t b) ∧
          polyline w' = clampBox s t '' polyline w) := by sorry

end FrechetNearLinear.Main
