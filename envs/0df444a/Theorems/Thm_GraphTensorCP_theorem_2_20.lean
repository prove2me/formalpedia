-- Prove2me | Theorems.Thm_GraphTensorCP_theorem_2_20
-- name    : GraphTensorCP.theorem_2_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:55.796671+00:00
-- url     : https://prove2.me/theorems/1a307bef-e3ea-4459-8b21-e8680488be9d
-- title:
--   Theorem 2.20 — Strassen's spectral duality: $\tilde R_{\mathbb F}(T)=\max_{\phi\in\Phi_{k,\mathbb F}}\phi(T)$ and $S\lesssim T\iff\phi(S)\le\phi(T)\ \forall\phi$
-- statement:
--   For every integer $k\ge2$ and every $k$-th order tensor $T$ over $\mathbb F$,
--
--   $$\tilde R_{\mathbb F}(T)=\max_{\phi\in\Phi_{k,\mathbb F}}\phi(T),$$
--
--   the maximum being attained. Moreover, for $k$-th order tensors $S,T$,
--
--   $$S\lesssim T\iff \phi(S)\le\phi(T)\ \text{ for every }\phi\in\Phi_{k,\mathbb F}.$$
--
--   This is Strassen's theorem (Strassen 1988; Christandl–Vrana–Zuiddam 2023; Wigderson–Zuiddam 2026), quoted by the paper. It turns asymptotic-rank bounds into inequalities for each spectral point and is used in Lemmas 2.28, 4.2 and Theorem 4.10.
--
--   **Formalization Note** Tensors are the published `MME.TensorObj K k`; the maximum is stated with `IsGreatest`, which includes attainment. The abstract version for a Strassen preorder is proved on the platform inside `mme_duality`; this item is the concrete statement for tensors, including $T=0$ (where both sides are $0$).
--
--   Differences from the source:
--   - encoding: $\tilde R_{\mathbb F}(T)=\lim_N R_{\mathbb F}(T^{\otimes N})^{1/N}$ → `MME.tensorAsymptoticRank` $=\inf_{N\ge1}R(T^{\otimes N})^{1/N}$; reason: the paper proves the limit equals this infimum (p.19); both are $0$ at $T=0$
--   - encoding: spectral points $\phi:\mathrm{Tens}_n(\mathbb F)\to\mathbb R_{\ge0}$ (Definition 2.19) → monotone semiring homomorphisms on the published quotient `MME.TensorQ` by mutual restriction (`Spec K n hn`); reason: a spectral point is constant on mutual-restriction classes and its four conditions are exactly "monotone semiring homomorphism"; same set of maps
--   - encoding: $\max_\phi\phi(T)$ → `IsGreatest` of the set of values $\phi(T)$; reason: "maximum" means a greatest attained value
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Theorem 2.20, p.22 (cited from [Str88, CVZ23, WZ26])

import Mathlib
import Definitions.Def_GraphTensorCP_specWeight
import Definitions.Def_GraphTensorCP_AsympRestrict
import Definitions.Def_mme_tensor_rank

universe u

namespace GraphTensorCP

/-- **Theorem 2.20** (Strassen's spectral duality [Str88, CVZ23, WZ26]), Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.22:
"For every integer k ≥ 2 and every k-th order tensor T, R̃_F(T) = max_{ϕ∈Φ_{k,F}} ϕ(T). Moreover, for
k-th order tensors S, T, we have S ≲ T if and only if ϕ(S) ≤ ϕ(T) for every ϕ ∈ Φ_{k,F}."

**Formalization Note.** Tensors are `MME.TensorObj K k`; `R̃_F` is `MME.tensorAsymptoticRank`
(`inf_{N≥1} R(T^{⊗N})^{1/N}`, equal to the limit, p.19; `0` at `T = 0`, as in Definition 2.13).
The maximum is stated as `IsGreatest` of the set of spectral values, so it is attained. `Φ_{k,F}` is
`Spec K k hk`, evaluated through `MME.TensorQ.toQ`; `≲` is `AsympRestrict` (Definition 2.14). The
statement includes `T = 0`. -/
theorem theorem_2_20 {K : Type u} [Field K] {k : ℕ} (hk : 1 < k) :
    (∀ T : MME.TensorObj K k,
      IsGreatest (Set.range fun φ : Spec K k hk => φ (MME.TensorQ.toQ T))
        (MME.tensorAsymptoticRank T)) ∧
    ∀ S T : MME.TensorObj K k,
      AsympRestrict S T ↔ ∀ φ : Spec K k hk, φ (MME.TensorQ.toQ S) ≤ φ (MME.TensorQ.toQ T) := by sorry

end GraphTensorCP
