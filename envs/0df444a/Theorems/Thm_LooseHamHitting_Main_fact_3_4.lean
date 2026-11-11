-- Prove2me | Theorems.Thm_LooseHamHitting_Main_fact_3_4
-- name    : LooseHamHitting.Main.fact_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:17:51.414195+00:00
-- url     : https://prove2.me/theorems/375247da-68de-47b9-9e9b-9efa2fb140c4
-- title:
--   Fact 3.4 — contraction/expansion identities for Ψ_{G,M}(x; y → z) and the exact ratio (3.1) in the complete 3-graph
-- statement:
--   Let $G$ be a 3-graph on $V$, $|V|=n$, let $M$ be a matching of $s\ge1$ pairs on $V$ with root pair $\{r_1,r_2\}\in M$ directed $r_1\to r_2$, and let $x,y,z\in V\setminus V(M)$ be distinct.
--
--   (i) $\Phi(G-x,M\cup\{yz\})=\Psi_{G,M}(x;y\to z)+\Psi_{G,M}(x;z\to y)$.
--
--   (ii) If $xyz\in G$, the number of $(G,M)$-respecting mixed Hamilton cycles containing $xyz$ is $\Phi(G-x,M\cup\{yz\})+\Phi(G-y,M\cup\{xz\})+\Phi(G-z,M\cup\{xy\})$.
--
--   (iii) If $\Phi(G,M)>0$ and $xyz\in G$, the proportion of $(G,M)$-respecting cycles traversing $\{x,y,z\}$ from $y$ to $z$ with $x$ private in the root orientation is $\Psi_{G,M}(x;y\to z)/\Phi(G,M)$.
--
--   (iv) If $G=\binom V3$, $n-s$ is even, $n-s\ge8$ and $n-3s\ge4$, then
--   $$\frac{\Psi_{G,M}(x;y\to z)}{\Phi(G,M)}=\frac{(n-3s)(n-3s-2)}{2(n-s-2)(n-2s)(n-2s-1)(n-2s-2)}.\tag{3.1}$$
--   If also $s=o(n)$, this ratio is $(1+o(1))/(2n^2)$: for every $\varepsilon>0$ there are $\eta>0$ and $N$ such that $n\ge N$ and $s\le\eta n$ give $|2n^2\,\Psi/\Phi-1|\le\varepsilon$.
--
--   The ratio (3.1) is the reference value against which the counts $\Psi$ are compared in §§9–11.
--
--   Differences from the source:
--   - encoding: if s = o(n), the ratio is (1 + o(1))/(2n²) → ∀ ε > 0, ∃ η > 0, ∃ N, every instance of (iv) with n ≥ N and s ≤ η n has |2n² Ψ/Φ − 1| ≤ ε; reason: explicit quantification of o(·) as n → ∞
--   - encoding: a root pair of M with a fixed direction → an ordered pair (r₁, r₂) with {r₁, r₂} ∈ M; reason: the direction is r₁ → r₂
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 10, Fact 3.4

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph

set_option autoImplicit false

open Classical

namespace LooseHamHitting.Main

/-- Fact 3.4: contraction/expansion identities for `Ψ_{G,M}(x; y → z)` and the ratio (3.1) in
the complete 3-graph. The root pair is `{r₁, r₂} ∈ M`, directed `r₁ → r₂`. -/
theorem fact_3_4 :
    (∀ (β : Type*) (V : Finset β) (G M : Finset (Finset β)) (r₁ r₂ x y z : β) (n s : ℕ),
      V.card = n → M.card = s → IsThreeGraph V G → IsMatching V M → 1 ≤ s → {r₁, r₂} ∈ M →
      x ∈ V \ matchedVerts M → y ∈ V \ matchedVerts M → z ∈ V \ matchedVerts M →
      x ≠ y → x ≠ z → y ≠ z →
      (Phi (V.erase x) (deleteVerts G {x}) (insert {y, z} M) =
          Psi V G M r₁ r₂ x y z + Psi V G M r₁ r₂ x z y) ∧
      (({x, y, z} : Finset β) ∈ G →
        ((mixedHamCycles V G M).filter (fun C => ({x, y, z} : Finset β) ∈ C)).card =
          Phi (V.erase x) (deleteVerts G {x}) (insert {y, z} M) +
            Phi (V.erase y) (deleteVerts G {y}) (insert {x, z} M) +
            Phi (V.erase z) (deleteVerts G {z}) (insert {x, y} M)) ∧
      (0 < Phi V G M → ({x, y, z} : Finset β) ∈ G →
        ((((mixedHamCycles V G M).filter
              (fun C => RootTraverses C r₁ r₂ {x, y, z} y z)).card : ℝ) / (Phi V G M : ℝ) =
          (Psi V G M r₁ r₂ x y z : ℝ) / (Phi V G M : ℝ))) ∧
      (G = V.powersetCard 3 → Even (n - s) → s + 8 ≤ n → 3 * s + 4 ≤ n →
        (Psi V G M r₁ r₂ x y z : ℝ) / (Phi V G M : ℝ) =
          ((n : ℝ) - 3 * s) * ((n : ℝ) - 3 * s - 2) /
            (2 * ((n : ℝ) - s - 2) * ((n : ℝ) - 2 * s) * ((n : ℝ) - 2 * s - 1) *
              ((n : ℝ) - 2 * s - 2)))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
      ∀ (β : Type*) (V : Finset β) (M : Finset (Finset β)) (r₁ r₂ x y z : β) (n s : ℕ),
        V.card = n → M.card = s → IsMatching V M → 1 ≤ s → {r₁, r₂} ∈ M →
        x ∈ V \ matchedVerts M → y ∈ V \ matchedVerts M → z ∈ V \ matchedVerts M →
        x ≠ y → x ≠ z → y ≠ z →
        Even (n - s) → s + 8 ≤ n → 3 * s + 4 ≤ n → N ≤ n → (s : ℝ) ≤ η * n →
        |(Psi V (V.powersetCard 3) M r₁ r₂ x y z : ℝ) / (Phi V (V.powersetCard 3) M : ℝ) *
            (2 * (n : ℝ) ^ 2) - 1| ≤ ε) := by sorry

end LooseHamHitting.Main
