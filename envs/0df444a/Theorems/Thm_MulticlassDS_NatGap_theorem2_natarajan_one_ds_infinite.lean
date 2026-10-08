-- Prove2me | Theorems.Thm_MulticlassDS_NatGap_theorem2_natarajan_one_ds_infinite
-- name    : MulticlassDS.NatGap.theorem2_natarajan_one_ds_infinite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:26:01.297045+00:00
-- url     : https://prove2.me/theorems/2cf64ad3-f58e-4b4a-b112-bdca468c60d1
-- title:
--   Theorem 2, p. 4 — a concept class with Natarajan dimension 1 and infinite DS dimension
-- statement:
--   There exist a domain $\mathcal X$, a label set $\mathcal Y$ and a concept class $\mathcal H \subseteq \mathcal Y^{\mathcal X}$ with
--   $$d_N(\mathcal H) = 1 \qquad\text{and}\qquad d_{DS}(\mathcal H) = \infty .$$
--
--   Since finite DS dimension is necessary for PAC learnability (Daniely and Shalev-Shwartz 2014), such a class is not PAC learnable, although its Natarajan dimension is finite. The Natarajan dimension therefore does not characterize multiclass learnability when the label set is infinite, which answers a question open since Natarajan's work in 1989.
--
--   **Formalization Note** Both dimensions are the shared $\mathbb N_\infty$-valued suprema; $d_{DS}(\mathcal H) = \top$ means that $\mathcal H$ DS-shatters sequences of every length, and the Natarajan dimension is required to equal $1$ exactly. The domain and label types are existentially quantified in `Type`.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 4, Theorem 2 (proof §5.4, p. 32)

import Mathlib
import Definitions.Def_MulticlassDS_NatGap_Dimensions

namespace MulticlassDS.NatGap

theorem theorem2_natarajan_one_ds_infinite :
    ∃ (X Y : Type) (H : Set (X → Y)), natarajanDim H = 1 ∧ dsDim H = ⊤ := by sorry

end MulticlassDS.NatGap
