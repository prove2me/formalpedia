-- Prove2me | Theorems.Thm_FrechetNearLinear_Main_lemma_4_7
-- name    : FrechetNearLinear.Main.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:36:41.874212+00:00
-- url     : https://prove2.me/theorems/5250f9df-a51e-48af-9011-7898c91c2a58
-- title:
--   Lemma 4.7 — boundary maps: R_r ⊆ T_B ⊆ R_{(F+4)r}, T_B is (r, F+4)-boundary information, certified propagation, linear-time witnesses
-- statement:
--   Let $r\ge0$ and let $B$ be an $(r,F)$-summary on the representative ports of a rectangle $R$, with boundary map $T_B=C_{\mathrm{out}}\circ\mathrm{Lift}(B)\circ C_{\mathrm{in}}$. Then
--   $$R_r\subseteq T_B\subseteq R_{(F+4)r}.$$
--   Hence $T_B$ is $(r,F+4)$-boundary information of $R$, and both min- and max-propagation through $T_B$ are $(r,F+4)$-certified: for labels in any linear order, if $\lambda'$ takes at each exit the minimum (maximum) of $\lambda(s)$ over $(s,t)\in T_B$, with $+\infty$ ($-\infty$) when there is none, then $\lambda'$ is an $(r,F+4)$-certified min- (max-) propagation of $\lambda$.
--
--   Given a decomposition $(s,s',t',t,e,g)$ of a pair of $T_B$ and a witness $\gamma$ for $(p_e,z_g)$, a witness for $(s,t)$ of cost at most $(F+4)r$ is obtained in time linear in the size of $\gamma$ plus the number of boundary edges between $s$ and $s'$ and between $t'$ and $t$: there are an admissible program $A$ and a constant $C$ such that for every such data, with $\gamma$ a bi-monotone polygonal path in $R\cap F_{Fr}$ given by its vertex list $w$ (input $p[0]=|w|$, $p[1],p[2]$ = side and index of $e$, $p[3],p[4]$ = side and index of $g$; memory the coordinates of $w$, then $x_0,x_1,y_0,y_1$, then $s,s',t',t$), $A$ accepts within
--   $$C\big(|w|+\beta_{\mathrm{in}}(s,s')+\beta_{\mathrm{out}}(t',t)+1\big)$$
--   steps and outputs the vertex list of a bi-monotone polygonal path from $s$ to $t$ in $R\cap F_{(F+4)r}$, where $\beta_{\mathrm{in}}$, $\beta_{\mathrm{out}}$ count the boundary-edge endpoints strictly between the two points.
--
--   Boundary maps are the stored relations through which every query of the algorithm propagates labels.
--
--   **Formalization Note** The machine is the mission's real RAM; edges are encoded as (side bit, integer index).
--
--   Differences from the source:
--   - reading: Definitions 2.2 and 4.2's "a witness … can be reported" → the witness exists; reason: the definitions attach no time bound to reporting
--   - generalization: labels "consist of a weight and a source identifier, ordered lexicographically" (p. 16) → labels in an arbitrary linear order `L`, with `WithTop L` / `WithBot L` for the unavailable values; reason: the paper's labels form a linear order, so it specializes
--   - reading: "Min- and max-propagation through $T_B$ take the minimum and maximum of $\lambda(s)$ over $(s,t)\in T_B$" → any $\lambda'$ satisfying `IsMinPropThrough`/`IsMaxPropThrough` (the extremum is attained, or $\pm\infty$ when no pair exists); reason: the literal content of Definition 4.6
--   - reading: "in time linear in the size of γ plus the number of boundary edges between s and s′ and between t′ and t" → within $C(|w|+\beta_{\mathrm{in}}+\beta_{\mathrm{out}}+1)$ steps on the mission's real RAM, with the decomposition and edges in the stated input layout; reason: the paper names no machine; the number of boundary edges between two points is at most the number of edge endpoints strictly between them plus one
-- source:
--   Huang, Wang, Zhang, Constant Approximation of Fréchet Distance in Near-Linear Time, STOC 2027 submission (manuscript sha256 08be7e65…dd2d), p. 16, Lemma 4.7

import Mathlib
import Definitions.Def_FrechetNearLinear_Main_FreeSpace
import Definitions.Def_FrechetNearLinear_Main_Machine

namespace FrechetNearLinear.Main

/-- Lemma 4.7 (Boundary maps), p. 16. Let `r ≥ 0` and let `B` be an `(r, F)`-summary on the
representative ports of `R`, with boundary map `T_B = C_out ∘ Lift(B) ∘ C_in`. (i)
`R_r ⊆ T_B ⊆ R_{(F+4)r}`. (ii) `T_B` is `(r, F + 4)`-boundary information of `R`. (iii) Min- and max-propagation of any
labelling through `T_B` are `(r, F + 4)`-certified. (iv) A fixed admissible program, given a
decomposition `(s, s', t', t, e, g)` of a pair of `T_B` and the vertex list `w` of a polygonal
witness for `(p_e, z_g)`, outputs the vertex list of a bi-monotone polygonal path from `s` to `t`
in `R ∩ F_{(F+4)r}` within `C · (|w| + β_in + β_out + 1)` steps, where `β_in`, `β_out` count the
boundary-edge endpoints strictly between `s` and `s'`, and between `t'` and `t`. -/
theorem lemma_4_7 :
    (∀ {d n m : ℕ} (P : Fin n → E d) (Q : Fin m → E d) (R : Rect n m) (r F : ℝ)
        (B : Bool × ℤ → Bool × ℤ → Prop), 0 ≤ r → IsRepSummary P Q R r F B →
        (∀ s t, Rrel P Q R r s t → boundaryMap P Q R r B s t) ∧
        (∀ s t, boundaryMap P Q R r B s t → Rrel P Q R ((F + 4) * r) s t) ∧
        IsBoundaryInfo P Q R r (F + 4) (boundaryMap P Q R r B) ∧
        (∀ (L : Type) [LinearOrder L] (lam lam' : ℝ × ℝ → WithTop L),
          IsMinPropThrough R (boundaryMap P Q R r B) lam lam' →
          IsCertifiedMinProp P Q R r (F + 4) lam lam') ∧
        (∀ (L : Type) [LinearOrder L] (lam lam' : ℝ × ℝ → WithBot L),
          IsMaxPropThrough R (boundaryMap P Q R r B) lam lam' →
          IsCertifiedMaxProp P Q R r (F + 4) lam lam')) ∧
    (∃ A : Program, Admissible A ∧ ∃ C : ℝ,
      ∀ {d n m : ℕ} (P : Fin n → E d) (Q : Fin m → E d) (R : Rect n m) (r F : ℝ)
        (B : Bool × ℤ → Bool × ℤ → Prop), 0 ≤ r → IsRepSummary P Q R r F B →
        ∀ (s s' t' t : ℝ × ℝ) (e g : Bool × ℤ) (w : List (ℝ × ℝ)),
          IsDecomposition P Q R r B s s' t' t e g →
          IsMonoPolyline w (repIn P Q R r e) (repOut P Q R r g) →
          polyline w ⊆ R.carrier ∩ freeSpace P Q (F * r) →
          ∃ w' : List (ℝ × ℝ),
            ComputesListWithin A
              (initCfg [(w.length : ℤ), (if e.1 then 1 else 0), e.2, (if g.1 then 1 else 0), g.2]
                (flatPts w ++ [R.x0, R.x1, R.y0, R.y1] ++ flatPts [s, s', t', t]))
              (C * ((w.length : ℝ) + R.inBreaksBetween s s' + R.outBreaksBetween t' t + 1)) w' ∧
            IsMonoPolyline w' s t ∧
            polyline w' ⊆ R.carrier ∩ freeSpace P Q ((F + 4) * r)) := by sorry

end FrechetNearLinear.Main
