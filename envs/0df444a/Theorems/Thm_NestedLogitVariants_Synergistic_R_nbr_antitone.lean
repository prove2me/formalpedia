-- Prove2me | Theorems.Thm_NestedLogitVariants_Synergistic_R_nbr_antitone
-- name    : NestedLogitVariants.Synergistic.R_nbr_antitone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:26:22.411168+00:00
-- url     : https://prove2.me/theorems/aa7150e0-315a-4236-b07e-b2f5508cc8b6
-- title:
--   Proof of Lemma 14, p. 43 — R_i(N_i,j−1) ≥ R_i(N_ij) for j = 2, …, n
-- statement:
--   For an instance with fully-captured nests ($v_{i0} = 0$), revenues ordered $r_{i1} \ge r_{i2} \ge \dots \ge r_{in}$ in each nest, and positive preference weights, the expected revenue of the nested-by-revenue assortments decreases along the nest: for every nest $i$ and every $j \in \{2, \dots, n\}$,
--
--   $$R_i(N_{ij}) \le R_i(N_{i,j-1}).$$
--
--   Indeed $R_i(N_{ij}) = \sum_{k=1}^j r_{ik} v_{ik} / \sum_{k=1}^j v_{ik}$ is a weighted average of the $j$ largest revenues of nest $i$. The fact gives $\alpha^1_{ik} \ge 1$ in the proof of Theorem 7 (p. 43) and the first half of Lemma 14.
--
--   **Formalization Note** The standing assumptions are those of the model (see the Model definition) and of §4: every nest is fully captured, $v_{i0} = 0$, and $\gamma_i > 1$ for some nest $i$ (p. 16). Revenues need only be nonnegative here. The range $j \ge 2$ excludes $R_i(N_{i0}) = R_i(\emptyset) = 0$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 43, proof of Lemma 14 (first two sentences), cited in Appendix A.1, p. 43

import Mathlib
import Definitions.Def_NestedLogitVariants_Synergistic_Model

namespace NestedLogitVariants.Synergistic

/-- Proof of Lemma 14, p. 43: since `r_{i1} ≥ ⋯ ≥ r_{in}`, `R_i(N_{ij})` is a weighted average of the
first `j` revenues of nest `i` and `R_i(N_{i,j−1}) ≥ R_i(N_{ij})` for `j = 2, …, n`. -/
theorem R_nbr_antitone {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (i : ι) (j : ℕ) (hj2 : 2 ≤ j) (hjn : j ≤ n) :
    R I i (nbr n j) ≤ R I i (nbr n (j - 1)) := by sorry

end NestedLogitVariants.Synergistic
