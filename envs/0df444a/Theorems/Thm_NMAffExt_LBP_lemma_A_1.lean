-- Prove2me | Theorems.Thm_NMAffExt_LBP_lemma_A_1
-- name    : NMAffExt.LBP.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:30:43.369821+00:00
-- url     : https://prove2.me/theorems/28f49eea-cf51-493c-9cd3-1dcea5ebb2d1
-- title:
--   Lemma A.1 — programs on $(X,R)$: a cut of at most $2s$ markers at pure-input rank $q$, projected sections, collision probability $2^{-(n-q)}$
-- statement:
--   Let $P$ be a weakly read-once linear branching program with $s$ vertices on $(X,R)\in\mathbb F_2^n\times\mathbb F_2^t$ (that is, on $n+t$ bits), and let $1\le q<n$. There is an equivalent full weakly read-once linear branching program $P'$ on $n+t$ bits and a set $V$ of at most $2s$ cut markers on edges of $P'$ such that every computation crosses exactly one marker of $V$, and for each marker $v\in V$ every path reaching it has the same prefix space $W_v$. Put $d_v=\dim W_v$. Then:
--
--   1. $\rho(W_v)=\dim(W_v\cap E_X)=q$ for every $v\in V$;
--   2. the crossing probabilities sum to one, $\sum_{v\in V}\Pr_{y\sim U_{n+t}}[y\text{ crosses }v]=1$; and for each $v\in V$ and each $Q_v\in\mathbb F_2^{d_v\times(n+t)}$ whose rows form a basis of $W_v$, there is $A_v\subseteq\mathbb F_2^{d_v}$ with: $y$ crosses $v$ iff $Q_vy\in A_v$, and $\Pr[y\text{ crosses }v]=p_v=|A_v|/2^{d_v}$;
--   3. for each such $v$ and $Q_v$ there are sections $\sigma_b:\mathbb F_2^{d_v}\to\mathbb F_2^{n+t}$, $b\in\mathbb F_2^{n+t-d_v}$, as in Lemma 4.7: each affine with $Q_v\sigma_b=\mathrm{id}$, images pairwise disjoint and covering $\mathbb F_2^{n+t}$, $(a,b)\mapsto\sigma_b(a)$ bijective, and a Boolean $P_v$ on $\mathbb F_2^{n+t-d_v}$ such that the subprogram started after the marker outputs $P_v(b)$ on $\sigma_b(a)$ and outputs $P(y)$ on every $y$ crossing $v$. Their projections $B_b=\pi_X\sigma_b$ satisfy
--   $$Q_0B_b(a)=Ja\qquad\text{(A.1)}$$
--   for a rank-$q$ matrix $Q_0\in\mathbb F_2^{q\times n}$ and a rank-$q$ matrix $J\in\mathbb F_2^{q\times d_v}$, both independent of $b$;
--   4. for every fixed $a$ and independent uniform $b,b'$,
--   $$\Pr_{b,b'}[B_b(a)=B_{b'}(a)]=2^{-(n-q)}.\qquad\text{(A.2)}$$
--
--   Differences from the source:
--   - encoding: a cut marker ("a designated point on an edge") → a `Marker` (vertex `src`, `label = some b` for the edge labelled $b$, or `none` for one point on both edges when they share their destination, as the proof does for an inserted query), required to be `Valid`; reason: the two kinds of marker placed in the proof (p. 101–102).
--   - reading: "let $W_v$ be its prefix space" → a clause that every path from the source to the marker's vertex has prefix span (its queries, the marker vertex's included) equal to $W_v$; reason: the proof's "At each marker, all reaching paths have the same prefix space", which makes $W_v$ well defined.
--   - encoding: "probabilities $p_v=|A_v|/2^{d_v}$ summing to one" → per marker, the crossing count over $2^{n+t}$ equals $|A_v|/2^{d_v}$, and the crossing probabilities sum to one; reason: $p_v$ is the crossing probability, so this is the same clause without a family of matrices indexed by markers of different dimensions.
--   - reading: "affine sections … as in Lemma 4.7" → the three items of Lemma 4.7 written out, with "the subprogram started at $v$" read as the subprogram started at the vertex the marked edge enters; reason: a marker is a point on an edge.
--   - encoding: $\mathbb F_2^{n+t-d_v}$ with natural-number subtraction; reason: $d_v\le n+t$, so nothing is truncated.
-- source:
--   Xin Li, Yan Zhong, Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds, arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 101 (PDF 103), Lemma A.1, eqs. (A.1)–(A.2)

import Mathlib
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_NMAffExt_LBP_Basic
import Definitions.Def_NMAffExt_LBP_Program
import Definitions.Def_NMAffExt_LBP_Markers

open Matrix

namespace NMAffExt.LBP

/-- **Lemma A.1.** Let `P` be a size-`s` weakly read-once linear branching program on
`(X, R) ∈ 𝔽₂ⁿ × 𝔽₂ᵗ` and `1 ≤ q < n`. There is an equivalent full weakly read-once program `P'` with a
cut `V` of at most `2s` markers, each computation crossing exactly one marker, such that at each
marker `v`, with prefix space `W v` (the same on every path reaching it), `d_v = dim W v` and `Q v`
a matrix whose rows are a basis of `W v`: (1) `ρ(W v) = q`; (2) reachability is `Q v (X, R) ∈ A_v`,
with probability `|A_v| / 2^{d_v}`, and these probabilities sum to one; (3) there are affine sections
`σ_b : 𝔽₂^{d_v} → 𝔽₂^{n+t}` (`b ∈ 𝔽₂^{n+t−d_v}`) as in Lemma 4.7 whose projections `B_b = π_X σ_b`
satisfy `Q₀ B_b(a) = J a` for rank-`q` maps `Q₀ : 𝔽₂ⁿ → 𝔽₂^q`, `J : 𝔽₂^{d_v} → 𝔽₂^q` independent of
`b`; (4) for every `a`, `Pr_{b,b'}[B_b(a) = B_{b'}(a)] = 2^{−(n−q)}`. -/
theorem lemma_A_1 (n t s q : ℕ) (P : Program (n + t) s) (hP : P.IsWeaklyReadOnce)
    (hq : 1 ≤ q) (hqn : q < n) :
    ∃ (s' : ℕ) (P' : Program (n + t) s'),
      P'.IsWeaklyReadOnce ∧ P'.IsFull ∧ (∀ y, P'.eval y = P.eval y) ∧
      ∃ (V : Finset (Marker s')) (W : Marker s' → Submodule (ZMod 2) (Fin (n + t) → ZMod 2)),
        V.card ≤ 2 * s ∧
        (∀ v ∈ V, v.Valid P') ∧
        (∀ y : Fin (n + t) → ZMod 2, ∃! v, v ∈ V ∧ v.Crosses P' y) ∧
        (∀ v ∈ V, ∀ l, P'.IsPathTo l v.src → P'.prefixSpan l = W v) ∧
        (∀ v ∈ V, pureRank (W v) = q) ∧
        ∑ v ∈ V, (Nat.card {y : Fin (n + t) → ZMod 2 // v.Crosses P' y} : ℝ) / 2 ^ (n + t) = 1 ∧
        ∀ v ∈ V, ∀ Q : Matrix (Fin (Module.finrank (ZMod 2) (W v))) (Fin (n + t)) (ZMod 2),
          RowsBasis Q (W v) →
          (∃ A : Finset (Fin (Module.finrank (ZMod 2) (W v)) → ZMod 2),
            (∀ y, v.Crosses P' y ↔ Q *ᵥ y ∈ A) ∧
            (Nat.card {y : Fin (n + t) → ZMod 2 // v.Crosses P' y} : ℝ) / 2 ^ (n + t) =
              (A.card : ℝ) / 2 ^ Module.finrank (ZMod 2) (W v)) ∧
          ∃ σ : (Fin (n + t - Module.finrank (ZMod 2) (W v)) → ZMod 2) →
              (Fin (Module.finrank (ZMod 2) (W v)) → ZMod 2) → (Fin (n + t) → ZMod 2),
            (∀ b, QuadExt.Main.IsAffineMap (σ b) ∧ ∀ a, Q *ᵥ σ b a = a) ∧
            (∀ b b', b ≠ b' → Disjoint (Set.range (σ b)) (Set.range (σ b'))) ∧
            (∀ y, ∃ b a, σ b a = y) ∧
            Function.Bijective (fun p : (Fin (Module.finrank (ZMod 2) (W v)) → ZMod 2) ×
                (Fin (n + t - Module.finrank (ZMod 2) (W v)) → ZMod 2) => σ p.2 p.1) ∧
            (∃ Pv : (Fin (n + t - Module.finrank (ZMod 2) (W v)) → ZMod 2) → ZMod 2,
              (∀ a b, P'.evalFrom (v.next P') (σ b a) = Pv b) ∧
              (∀ y, v.Crosses P' y → P'.evalFrom (v.next P') y = P'.eval y)) ∧
            ∃ (Q₀ : Matrix (Fin q) (Fin n) (ZMod 2))
              (J : Matrix (Fin q) (Fin (Module.finrank (ZMod 2) (W v))) (ZMod 2)),
              Q₀.rank = q ∧ J.rank = q ∧
              (∀ b a, Q₀ *ᵥ projX (σ b a) = J *ᵥ a) ∧
              ∀ a, avg (fun bb : (Fin (n + t - Module.finrank (ZMod 2) (W v)) → ZMod 2) ×
                  (Fin (n + t - Module.finrank (ZMod 2) (W v)) → ZMod 2) =>
                  if projX (σ bb.1 a) = projX (σ bb.2 a) then (1 : ℝ) else 0) =
                (2 : ℝ) ^ (-((n : ℤ) - q)) := by sorry

end NMAffExt.LBP
