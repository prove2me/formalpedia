-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_42
-- name    : MonoidProdQ.Supplement.theorem_42
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:22:06.290215+00:00
-- url     : https://prove2.me/theorems/9670f26c-8fd8-42db-9b7e-4778d370fc94
-- title:
--   Theorem 42 — tree search with shared subcomputations: a dual of cost $C_\rho$ and $Q_{1/3}(F)=O(C_\rho)$
-- statement:
--   Let $T$ be a finite rooted tree with root $\rho$ and root-to-$v$ paths $P(v)$ (both endpoints included). Let $D\subseteq\Sigma^n$ be a promise set, and for each vertex $v$ let $g_v:D\to\Gamma_v$ have an all-pairs dual of cost at most $t_v>0$; all alphabets are finite. A vertex $v$ is marked when a fixed predicate of $(g_w(x))_{w\in P(v)}$ holds, and $F(x)=1$ if some vertex is marked, $F(x)=0$ otherwise. Define
--   $$C_v=t_v+\sqrt{\sum_{u\text{ child of }v}C_u^2}\tag{48}$$
--   ($C_v=t_v$ at a leaf). Then
--
--   1. $F$ has an all-pairs dual of cost at most $C_\rho$, and
--   2. $Q_{1/3}(F)\le K\,C_\rho$ with a universal constant $K$.
--
--   The functions $g_v$ may read overlapping input positions.
--
--   **Formalization Note** The tree is the published rooted-tree model; $P(v)$ and $C_v$ are the definitions `treePath` and `treeCost`. The predicate of $v$ is a Boolean function of the full answer vector that depends only on the entries on $P(v)$.
--
--   Differences from the source:
--
--   - generalization: input positions [n] (D ⊆ Σⁿ) → any finite nonempty type I of positions; reason: specializes to I = Fin n
--   - encoding: n ≥ 1 (implicit) → [Nonempty I]; reason: with no position the platform's query register is empty and Q_{1/3} = ⊤
--   - encoding: a fixed predicate of (g_w(x))_{w∈P(v)} → a Boolean function of the whole answer vector, invariant under changes off P(v); reason: same predicates
--   - encoding: O(C_ρ) → ∃ universal K > 0; reason: an O-bound with a universal constant
--   - encoding: F(x) ∈ {0, 1} → F(x) = decide (∃ v, v marked) ∈ Bool; reason: true/false for 1/0, same function
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 42 (Tree search with shared subcomputations), pp.58–59

import Definitions.Def_MonoidProdQ_Q13
import Definitions.Def_MonoidProdQ_DualFeasible
import Definitions.Def_MonoidProdQ_dualCost
import Definitions.Def_MonoidProdQ_Supplement_treePath
import Definitions.Def_MonoidProdQ_Supplement_treeCost

open scoped ENNReal
open HarelTarjan.Compressed

universe u v w x

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 42 (Tree search with shared
subcomputations), pp.58–59: "Let T be a finite rooted tree with root ρ, and let P(v) be the
root-to-v path, including both endpoints. For each vertex v, let g_v : D → Γ_v, where D ⊆ Σⁿ, be
a deterministic function with an all-pairs dual of cost at most t_v > 0. All input and output
alphabets are finite. A vertex v is marked when a fixed predicate of (g_w(x))_{w∈P(v)} holds.
Let F(x) = 1 if some vertex is marked, and F(x) = 0 otherwise. Define
C_v = t_v + √(Σ_{u child of v} C_u²), (48) with the empty sum equal to zero, so C_v = t_v at a
leaf. Then F has an all-pairs dual of cost at most C_ρ, and Q_{1/3}(F) = O(C_ρ). The functions
g_v may depend on overlapping input positions." One universal `K > 0` such that, under these
hypotheses,

1. `F` has an all-pairs dual (`DualFeasible`) of cost (`dualCost`) at most `C_ρ` (no constant);
2. `Q_{1/3}(F) ≤ K·C_ρ`.

**Formalization Note.** The tree is the published `HarelTarjan.Compressed.RootedTree` on a
finite vertex type `V` (root and parent map), `P(v)` is `treePath T v` and `C_v` is
`treeCost T t v` (Eq. (48) unfolded `|V|` times, which reaches the fixed point). Input positions
are a finite nonempty type `I` (the paper's `[n]`, `n ≥ 1`; with no position the platform's
query register is empty), letters a finite type `Sig`, and `D` a promise set of words. The
predicate of `v` is a Boolean function `mark v` of the whole vector `(z_w)_w` of answers that
depends only on the entries on `P(v)` (hypothesis `hmark`); `F(x) ∈ {0, 1}` is the Boolean
`decide (∃ v, mark v (g · x))`. The `g_v` are arbitrary functions of the whole input. -/
theorem theorem_42 :
    ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (T : RootedTree V)
        (I : Type v) (Sig : Type w) [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Sig]
        [DecidableEq Sig] (Γ : V → Type x) [∀ v, Fintype (Γ v)] [∀ v, DecidableEq (Γ v)]
        (D : Finset (I → Sig)) (g : ∀ v, (I → Sig) → Γ v) (t : V → ℝ),
        (∀ v, 0 < t v) →
        (∀ v, ∃ (d : ℕ) (a b : D → I → EuclideanSpace ℂ (Fin d)),
          DualFeasible (g v) D a b ∧ (dualCost a b : ℝ) ≤ t v) →
        ∀ mark : V → (∀ w, Γ w) → Bool,
        (∀ v (z z' : ∀ w, Γ w), (∀ w ∈ treePath T v, z w = z' w) → mark v z = mark v z') →
          (∃ (d : ℕ) (a b : D → I → EuclideanSpace ℂ (Fin d)),
            DualFeasible (fun y => decide (∃ v, mark v (fun w => g w y) = true)) D a b ∧
              (dualCost a b : ℝ) ≤ treeCost T t T.root) ∧
          (Q13 (fun y => decide (∃ v, mark v (fun w => g w y) = true)) D : ℝ≥0∞) ≤
            ENNReal.ofReal (K * treeCost T t T.root) := by sorry

end MonoidProdQ.Supplement
