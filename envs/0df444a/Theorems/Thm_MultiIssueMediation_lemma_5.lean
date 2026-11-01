-- Prove2me | Theorems.Thm_MultiIssueMediation_lemma_5
-- name    : MultiIssueMediation.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:52.14043+00:00
-- url     : https://prove2.me/theorems/7e9cc14a-386d-4c50-812f-c9a857f3c135
-- title:
--   Lemma 5 — where a beaten bundle can appear (corrected: $a\ne b$ in the construction of $\triangleright_f$)
-- statement:
--   Let $f$ be efficient, individually rational and strategy-proof, $m\ge 2$, with $\triangleright_f$ the relation of Step 2.
--
--   1. Let $a=f_{\ell,j}$ and $b=f_{\ell-1,j-1}$ be bundles of $\mathbf B$ with $a\triangleright_f b$. Then there is no $k\ge\ell$ and $r$ with $f_{k,r}=b$, and there is no $\ell'<\ell$ and $j'<j$ with $f_{\ell',j'}=a$.
--   2. Let $c=f_{\ell,j}$ and $d=f_{\ell+1,j+1}$ be bundles of $\mathbf B$ with $c\triangleright_f d$. Then there is no $k\le j$ and $r$ with $f_{r,k}=d$, and there is no $\ell'>\ell$ and $j'>j$ with $f_{\ell',j'}=c$.
--
--   These location facts drive the exclusion of 3-cycles in Lemma 6.
--
--   Differences from the source:
--   - correction: f_{ℓ−1,j} ▷ f_{ℓ,j+1} whenever f_{ℓ,j} = f_{ℓ−1,j}, and symmetrically (p.35) → the relation ▷_f holds only between distinct bundles a ≠ b; reason: as printed, equal neighbours give a ▷ a and Lemma 4 is false: m = 3, an adjacent rule with b_2 on top, cell (3,1); the proof of Lemma 4 speaks of diagonally adjacent, hence distinct, bundles
--   - reading: "diagonally adjacent from below" and "from above", defined with "a lies on a higher row" → (i) has b = f_{ℓ−1,j−1} and (ii) has d = f_{ℓ+1,j+1}; reason: here "higher row" means the larger row index, as the proofs of Lemmas 5 and 6 (pp.35–36) show; the lemma's own "i.e." clauses agree
--   - reading: a consistent extension map Λ; Definition 1 constrains it from one side and Theorem 1 does not name it → Λ(θ_i) is the set of all consistent orderings (admissibleOrderings); reason: it is the only reading under which Theorem 1 is true (singleton maps give a counterexample at m = 3) and the one the proof uses, pp.28–29
--   - reading: there exists a one-to-one mapping t_i : X → Y → the fixed map t(x_k) = y_{m+1−k}, t(o_X) = o_Y, for both negotiators; reason: Example 1 (pp.13–14) and the definition of B (p.14) fix it; t(o_X) is never used
--   - encoding: types in Θ_i, m+1 positions of o_X → the m rows and m columns of the paper's matrix, indexed by Fin m; reason: the paper's own domain M × M (p.15), which leaves out the type that accepts nothing
--   - encoding: indices 1, …, m, outside options o_X, o_Y, cells f_{ℓ−1,j}, f_{ℓ,j+1} → Fin m with value = index − 1, Option (Fin m) with none the outside option, Fin.rev for m+1−k, indices p, q with p + 1 = ℓ, q = j + 1; reason: Lean conventions; the instances are the same
-- source:
--   Kesten, Özyurt, Efficient and Incentive Compatible Mediation: An Ordinal Market Design Approach, working paper, 4 October 2018, Lemma 5, p.35

import Mathlib
import Definitions.Def_MultiIssueMediation_RuleGeometry

namespace MultiIssueMediation

/-- **Lemma 5** (Kesten, Özyurt, *Efficient and Incentive Compatible Mediation: An Ordinal Market
Design Approach*, working paper, 4 October 2018, Lemma 5, p.35), for an efficient, individually
rational and strategy-proof rule and the relation `▷_f` of Step 2.

(i) If `a = f_{ℓ,j}`, `b = f_{ℓ−1,j−1}` and `a ▷_f b`, then there is no `k ≥ ℓ` and `r` with
`f_{k,r} = b`, and there is no `ℓ' < ℓ` and `j' < j` with `f_{ℓ',j'} = a`.

(ii) If `c = f_{ℓ,j}`, `d = f_{ℓ+1,j+1}` and `c ▷_f d`, then there is no `k ≤ j` and `r` with
`f_{r,k} = d`, and there is no `ℓ' > ℓ` and `j' > j` with `f_{ℓ',j'} = c`.

**Formalization Note.** "Diagonally adjacent from below" and "from above" are spelled out with
indices, as in the proofs of Lemmas 5 and 6 (pp.35–36): in (i) `p` is row `ℓ−1` and `q` is column
`j−1`, in (ii) `p` is row `ℓ+1` and `q` is column `j+1`. -/
theorem lemma_5 {m : ℕ} (hm : 2 ≤ m) (f : MediationRule m) (hE : Efficient f)
    (hIR : IndividuallyRational f) (hSP : StrategyProof f) :
    (∀ (a b : logrollBundles m) (ℓ j p q : Fin m), p.val + 1 = ℓ.val → q.val + 1 = j.val →
      f ℓ j = a → f p q = b → derivedPrec f a b →
        (∀ k r : Fin m, ℓ ≤ k → f k r ≠ b) ∧
          (∀ ℓ' j' : Fin m, ℓ' < ℓ → j' < j → f ℓ' j' ≠ a)) ∧
      (∀ (c d : logrollBundles m) (ℓ j p q : Fin m), p.val = ℓ.val + 1 → q.val = j.val + 1 →
        f ℓ j = c → f p q = d → derivedPrec f c d →
          (∀ k r : Fin m, k ≤ j → f r k ≠ d) ∧
            (∀ ℓ' j' : Fin m, ℓ < ℓ' → j < j' → f ℓ' j' ≠ c)) := by sorry

end MultiIssueMediation
