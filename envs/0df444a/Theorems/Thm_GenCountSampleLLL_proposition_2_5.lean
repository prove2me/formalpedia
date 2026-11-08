-- Prove2me | Theorems.Thm_GenCountSampleLLL_proposition_2_5
-- name    : GenCountSampleLLL.proposition_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:53:44.083196+00:00
-- url     : https://prove2.me/theorems/ceba7161-46e2-4ab8-8b9e-2d7589d6293e
-- title:
--   Proposition 2.5, p.10 — the 2-tree recursion for $\mu_{\mathcal D^-}-\mu_{\mathcal D}$
-- statement:
--   Assume (1.1) with $c=1/100$ for some $x\in(0,1)^{\mathcal C}$. For every $a\in\mathcal D\subseteq\mathcal C$,
--   $$
--   \mu_{\mathcal D^-}-\mu_{\mathcal D}=\sum_{\mathcal T\in\mathfrak T_{\mathcal D,a}}\lambda_{\mathcal T}(\mathbf 1_{E_{\mathcal T}}-\theta_{\mathcal T})\mu_{\mathcal D_{\mathcal T}}+\sum_{\mathcal T\in\mathfrak T_{\mathcal D,a}}\lambda_{\mathcal T}\theta_{\mathcal T}\sum_{i=1}^{\ell(\mathcal T)}\big(\mu_{\mathcal D_{\mathcal T,i-1}}-\mu_{\mathcal D_{\mathcal T,i}}\big),
--   $$
--   where $\lambda_{\mathcal T}=(-1)^{|\mathcal T|-1}Z_{\mathcal D_{\mathcal T}}/Z_{\mathcal D}$ and $(\mathbf 1_{E_{\mathcal T}}-\theta_{\mathcal T})\mu_{\mathcal D_{\mathcal T}}$ is the signed measure $\sigma\mapsto(\mathbf 1_{E_{\mathcal T}}(\sigma)-\theta_{\mathcal T})\mu_{\mathcal D_{\mathcal T}}(\sigma)$.
--
--   The insertion chain implements this recursion: the first sum by resampling $U_{\mathcal T}$, the second through corridors of smaller chains.
--
--   Differences from the source:
--   - encoding: the standing assumption of §2, p.7: "Throughout the proof, we assume (1.1) with c = 1/100", with x ∈ (0,1)^𝒞 → explicit hypotheses `hx : ∀ b, 0 < x b ∧ x b < 1` and `hLLL : I.LLLCond (1/100) x`; reason: the statement on the page omits the section's standing assumption; the Lean states it
--   - encoding: an identity of signed measures on Ω → an equality of real functions at every assignment σ; reason: Ω is finite
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Proposition 2.5, p.10

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst
import Definitions.Def_GenCountSampleLLL_twoTrees

set_option autoImplicit false

open scoped BigOperators ENNReal

open Classical

namespace GenCountSampleLLL

open Inst

/-- Proposition 2.5, p.10 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)), under (1.1) with `c = 1/100`. For every
`a ∈ D ⊆ C`,
`µ_{D⁻} − µ_D = Σ_{T ∈ T_{D,a}} λ_T (1_{E_T} − θ_T) µ_{D_T}
  + Σ_{T ∈ T_{D,a}} λ_T θ_T Σ_{i=1}^{ℓ(T)} (µ_{D_{T,i−1}} − µ_{D_{T,i}})`.

**Formalization Note.** An identity of real functions on `Ω`, stated at every assignment `σ`. -/
theorem proposition_2_5 (I : Inst) (x : Fin I.m → ℝ) (hx : ∀ b, 0 < x b ∧ x b < 1)
    (hLLL : I.LLLCond (1 / 100) x) (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D)
    (σ : I.Assign) :
    I.mu (D.erase a) σ - I.mu D σ =
      ∑ T ∈ I.twoTrees D a,
          I.lam D T * ((if I.inET D a T σ then 1 else 0) - I.theta D a T) * I.mu (I.DT D T) σ +
        ∑ T ∈ I.twoTrees D a, I.lam D T * I.theta D a T *
          ∑ i ∈ Finset.Icc 1 (I.ell D a T),
            (I.mu (I.DTi D a T (i - 1)) σ - I.mu (I.DTi D a T i) σ) := by sorry

end GenCountSampleLLL
