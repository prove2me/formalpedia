-- Prove2me | Theorems.Thm_ImplicitParityWL_lemma_5_6
-- name    : ImplicitParityWL.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:18:01.356008+00:00
-- url     : https://prove2.me/theorems/250dd156-776e-4564-a149-25aad72c7c2e
-- title:
--   Lemma 5.6 — following an inference
-- statement:
--   Fix a schema $e$ and an equation $X_{u,\sigma a}+X_{v,\tau a}+X_{w,\pi a}=0$ of it, and consider the inference of $X_{w,\pi a}=b$ from $X_{u,\sigma a}=b_1$ and $X_{v,\tau a}=b_2$, with $b=b_1+b_2$. Suppose $k$ pebble pairs match $\mathrm{crd}_{w,\pi(c)}[0]\leftrightarrow\mathrm{crd}_{w,\pi(c)}[b_c]$ for every $c\in\mathrm{supp}(a)$, with observed value $\sum_cb_c=1-b$. With one additional pebble pair and $O(k^2)$ moves, Spoiler can either win or reach one of the game states
--   $$
--   \mathrm{crd}_{u,\sigma(c)}[0]\leftrightarrow\mathrm{crd}_{u,\sigma(c)}[\alpha_c],\ \ \sum_c\alpha_c=1-b_1,\qquad\text{or}\qquad
--   \mathrm{crd}_{v,\tau(c)}[0]\leftrightarrow\mathrm{crd}_{v,\tau(c)}[\beta_c],\ \ \sum_c\beta_c=1-b_2,
--   $$
--   for every $c\in\mathrm{supp}(a)$. The same guarantee holds for binary equations.
--
--   So a discrepancy at a conclusion moves to a discrepancy at a premise, which turns a refutation into a winning strategy for Spoiler.
--
--   **Formalization Note** The constant in $O(k^2)$ is absolute. The statement has one clause per position of the conclusion: at $w$, at $u$ and at $v$ for a ternary schema, and at $v$ and at $u$ for a binary one, where both sides of the equation carry the same bit $b_1$.
--
--   Differences from the source:
--   - reading: the lemma is printed for a conclusion at w; the next sentence says it is symmetric in the choice of conclusion and the proof of Theorem 5.7 uses this → clauses for a conclusion at w, at u and at v, and both directions of a binary equation; reason: the stronger reading; the printed statement is the first clause, and the strip is not symmetric, so the other positions must be stated
--   - encoding: O(k²) moves → ∃ absolute C, Forces (C * k ^ 2); reason: the constant is chosen before k, ℓ and the system
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Lemma 5.6, p.28, and the sentence following it

import Mathlib
import Definitions.Def_ImplicitParityWL_CompiledGraph

namespace ImplicitParityWL

/-- **Lemma 5.6** (Following an inference; Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.28): fix a schema `e` and the equation `X_{u,σa} + X_{v,τa} + X_{w,πa} = 0` at
an allowed address `a`, and the inference `X_{u,σa} = b₁`, `X_{v,τa} = b₂` ⊢ `X_{w,πa} = b₁ + b₂`. If `k` pebble pairs match
`crd_{w,π(c)}[0] ↔ crd_{w,π(c)}[b_c]` for every `c ∈ supp(a)` with observed value `1 - (b₁ + b₂)`, then with one additional
pebble pair and `O(k²)` moves Spoiler can either win or reach a state with the discrepancy at a premise:
`crd_{u,σ(c)}[0] ↔ crd_{u,σ(c)}[α_c]` with `∑ α_c = 1 - b₁`, or `crd_{v,τ(c)}[0] ↔ crd_{v,τ(c)}[β_c]` with `∑ β_c = 1 - b₂`.
The same guarantee holds for binary equations.

**Formalization Note** The sentence after the lemma on p.28 states that the lemma "is symmetric in the choice of conclusion:
`u` or `v` can play the role of `w`", and the proof of Theorem 5.7 uses this. All three positions of the conclusion are
therefore stated, and for a binary schema both directions; in a binary equation both sides have the same bit `b₁`. The
constant `C` is absolute. -/
theorem lemma_5_6 : ∃ C : ℕ, ∀ (k ℓ : ℕ), 3 ≤ k → 1 ≤ ℓ →
    ∀ {W E : Type} [Fintype W] [Fintype E] (I : ImplicitSystem k ℓ W E) (e : E) (a : Address k ℓ),
      a.supp ⊆ (I.schema e).dom →
      ∀ (S : GameState (I.Vertex 0) (I.Vertex 1) (k + 1)) (bits : Coord k ℓ → ZMod 2) (b₁ b₂ : ZMod 2),
        let u := (I.schema e).u
        let v := (I.schema e).v
        let σ := (I.schema e).σ
        let τ := (I.schema e).τ
        let G₀ := I.graph 0
        let G₁ := I.graph 1
        let Disc (L : Coord k ℓ → ZMod 2 → Vtx k ℓ W E) (b : ZMod 2)
            (S' : GameState (I.Vertex 0) (I.Vertex 1) (k + 1)) : Prop :=
          ∃ γ : Coord k ℓ → ZMod 2, I.PebbleMatch S' L a γ ∧ ∑ c ∈ a.supp, γ c = 1 - b
        (∀ (w : W) (π : BlockPerm k ℓ), (I.schema e).third = some (w, π) →
          ((I.PebbleMatch S (crdFamily w π) a bits ∧
              ∑ c ∈ a.supp, bits c = 1 - (b₁ + b₂)) →
            Forces G₀ G₁ (C * k ^ 2) S (fun S' =>
              Disc (crdFamily u σ) b₁ S' ∨ Disc (crdFamily v τ) b₂ S')) ∧
          ((I.PebbleMatch S (crdFamily u σ) a bits ∧ ∑ c ∈ a.supp, bits c = 1 - (b₁ + b₂)) →
            Forces G₀ G₁ (C * k ^ 2) S (fun S' =>
              Disc (crdFamily v τ) b₁ S' ∨ Disc (crdFamily w π) b₂ S')) ∧
          ((I.PebbleMatch S (crdFamily v τ) a bits ∧ ∑ c ∈ a.supp, bits c = 1 - (b₁ + b₂)) →
            Forces G₀ G₁ (C * k ^ 2) S (fun S' =>
              Disc (crdFamily u σ) b₁ S' ∨ Disc (crdFamily w π) b₂ S'))) ∧
        ((I.schema e).third = none →
          ((I.PebbleMatch S (crdFamily v τ) a bits ∧ ∑ c ∈ a.supp, bits c = 1 - b₁) →
            Forces G₀ G₁ (C * k ^ 2) S (Disc (crdFamily u σ) b₁)) ∧
          ((I.PebbleMatch S (crdFamily u σ) a bits ∧ ∑ c ∈ a.supp, bits c = 1 - b₁) →
            Forces G₀ G₁ (C * k ^ 2) S (Disc (crdFamily v τ) b₁))) := by sorry

end ImplicitParityWL
