-- Prove2me | Theorems.Thm_FrechetNearLinear_Main_lemma_4_15
-- name    : FrechetNearLinear.Main.lemma_4_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:36:48.274936+00:00
-- url     : https://prove2.me/theorems/fdde5a2e-b1f3-49d9-9d15-9be4a54d23ee
-- title:
--   Lemma 4.15 — boundary information composes over a partition into rectangles (transitive closure)
-- statement:
--   Let $R=R_1\cup\dots\cup R_N$ for rectangles $R_i$ with pairwise disjoint interiors, let $r\ge0$, $C\ge1$, and let $B_i$ be $(r,C)$-boundary information of $R_i$. Then
--   $$B=(\mathrm{In}(R)\times\mathrm{Out}(R))\cap(B_1\cup\dots\cup B_N)^+$$
--   is $(r,C)$-boundary information of $R$, where $^+$ is the transitive closure. A witness is obtained by concatenating the local witnesses along a chain in this closure: every pair $(s,t)$ of $B$ has a chain $s=u_0,u_1,\dots,u_{k+1}=t$ with $(u_{j},u_{j+1})\in B_{i_j}$, and for any local witnesses $\pi_j$ (bi-monotone paths from $u_j$ to $u_{j+1}$ in $R_{i_j}\cap F_{Cr}$) there is a bi-monotone path from $s$ to $t$ in $R\cap F_{Cr}$ whose point set is $\bigcup_j\pi_j$.
--
--   This is why crossing several rectangles does not increase the approximation factor.
--
--   Differences from the source:
--   - reading: "A witness is obtained by concatenating the local witnesses along a chain in this closure" → every pair of $B$ has a chain in the closure, and the local witnesses along it concatenate to a bi-monotone path in $R\cap F_{Cr}$ with their union as point set; reason: the literal content; Definition 2.2 attaches no time bound to reporting
--   - encoding: $R_1,\dots,R_N$ and $B_1,\dots,B_N$ → families indexed by `Fin N`, relations as predicates, closure as `Relation.TransGen`; reason: Lean convention, same objects
-- source:
--   Huang, Wang, Zhang, Constant Approximation of Fréchet Distance in Near-Linear Time, STOC 2027 submission (manuscript sha256 08be7e65…dd2d), p. 20, Lemma 4.15

import Mathlib
import Definitions.Def_FrechetNearLinear_Main_FreeSpace

namespace FrechetNearLinear.Main

/-- Lemma 4.15 (Boundary information composes), p. 20. If `R = R₁ ∪ ⋯ ∪ R_N` for rectangles with
pairwise disjoint interiors and `Bᵢ` is `(r, C)`-boundary information of `Rᵢ`, then
`B = (In(R) × Out(R)) ∩ (B₁ ∪ ⋯ ∪ B_N)⁺` is `(r, C)`-boundary information of `R`, and every pair
of `B` has a witness obtained by concatenating local witnesses along a chain of the closure. -/
theorem lemma_4_15 {d n m : ℕ} (P : Fin n → E d) (Q : Fin m → E d) (R : Rect n m) (N : ℕ)
    (Rs : Fin N → Rect n m) (hcover : R.carrier = ⋃ i, (Rs i).carrier)
    (hdisj : Pairwise fun i j => Disjoint (interior (Rs i).carrier) (interior (Rs j).carrier))
    (r C : ℝ) (hr : 0 ≤ r) (hC : 1 ≤ C) (B : Fin N → ℝ × ℝ → ℝ × ℝ → Prop)
    (hB : ∀ i, IsBoundaryInfo P Q (Rs i) r C (B i)) :
    IsBoundaryInfo P Q R r C
      (fun s t => s ∈ R.inB ∧ t ∈ R.outB ∧ Relation.TransGen (fun a b => ∃ i, B i a b) s t) ∧
    ∀ s t, s ∈ R.inB → t ∈ R.outB → Relation.TransGen (fun a b => ∃ i, B i a b) s t →
      ∃ (k : ℕ) (u : Fin (k + 2) → ℝ × ℝ) (idx : Fin (k + 1) → Fin N),
        u 0 = s ∧ u (Fin.last (k + 1)) = t ∧
        (∀ j : Fin (k + 1), B (idx j) (u j.castSucc) (u j.succ)) ∧
        ∀ π : ∀ j : Fin (k + 1), Path (u j.castSucc) (u j.succ),
          (∀ j, BiMono (π j) ∧ ∀ w, π j w ∈ (Rs (idx j)).carrier ∩ freeSpace P Q (C * r)) →
          ∃ γ : Path s t, BiMono γ ∧ Set.range γ = ⋃ j, Set.range (π j) ∧
            ∀ w, γ w ∈ R.carrier ∩ freeSpace P Q (C * r) := by sorry

end FrechetNearLinear.Main
