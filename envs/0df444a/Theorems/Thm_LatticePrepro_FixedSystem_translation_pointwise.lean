-- Prove2me | Theorems.Thm_LatticePrepro_FixedSystem_translation_pointwise
-- name    : LatticePrepro.FixedSystem.translation_pointwise
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:44.09202+00:00
-- url     : https://prove2.me/theorems/63fee778-7104-492d-9dd9-c36f096b23bc
-- title:
--   Pointwise translation identity for light solutions (soundness of Theorem 4.6)
-- statement:
--   Let $p$ be a prime, $K$ a field that is an $\mathbb{F}_p$-algebra, and $\Omega$ an extension field of $K$. Elements of $\mathbb{F}_p$ and $K$ are viewed in $\Omega$ through the algebra maps. Consider the fixed-verifier system of Construction 4.5 for a quadratic verifier $V$ (instance length $n$, $S$ coordinates), a moment representation $R$ over $K$ (moment parameter $r$, moment maps $\hat M_k$) and an encoding tuple $(E_i)$. Let $\theta_x=\sum_{i=1}^nx_iE_i+E_{n+1}$. Let $x\in\{0,1\}^n$ and let $v$ satisfy all equations of the system for $x$. Suppose that every table $T$ has a finitely supported coefficient function $f_T:\Omega\to\mathbb{F}_p$ such that
--   - $\hat M_k(v_T)=\mu_k(f_T):=\sum_{\alpha}f_T(\alpha)\,\alpha^k$ in $\Omega$, for every table $T$ and every $0\le k\le2r-2$;
--   - $\sum_T|\operatorname{supp}f_T|<r$.
--
--   Write $f_{0,0}$ for the function of the main table $v_{0,0}$ and $f^{(i)}$ for that of the auxiliary table $v^{(i)}$, $n+1<i\le S$. Then for every $\alpha\in\Omega$,
--   $$f_{0,0}(\alpha)-\sum_{i=n+2}^{S}\bigl(f^{(i)}(\alpha-E_i)-f^{(i)}(\alpha)\bigr)=\mathbf{1}[\alpha=\theta_x].$$
--
--   This is the translation identity (19) of the paper. The soundness proof of Theorem 4.6 shows that it holds pointwise for solutions below the weight threshold. Summing it over the coset $\theta_x+\operatorname{span}_{\mathbb{F}_p}\{E_i: i>n+1\}$ then gives $\sum f_{0,0}=1$ on that coset.
--
--   **Formalization Note** Lean writes the identity as "left-hand side minus `Finsupp.single θ_x 1` evaluated at $\alpha$ equals $0$". The functions are `Ω →₀ ZMod p` indexed by `TblIdx`, and $f_{0,0}$ is the function at index `rep 0 0`. The support hypothesis sums over all tables, product and auxiliary. The moment hypothesis is stated after mapping $K$ into $\Omega$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Theorem 4.6 (\label{thm:fixed-verifier-reduction}), step of the soundness proof establishing the translation identity (19) (\label{eq:strategy-target}) pointwise; Lean: LatticePrepro/Reduction/Soundness.lean, LatticePrepro.FixedSystem.translation_pointwise

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem

open LatticePrepro
open Finsupp
open LatticePrepro.FixedSystem
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)
variable {x : Fin V.n → Bool} {v : Col V R → ZMod p} (hv : Solves V R ε x v)
  (f : V.TblIdx → Ω →₀ ZMod p)
  (hf : ∀ T (k : R.Order), algebraMap K Ω (R.momentMap k (tbl V R v T)) = moment (f T) k)
  (hN : ∑ T, (f T).support.card < R.r)
include hv hf hN

theorem LatticePrepro.FixedSystem.translation_pointwise (α : Ω) :
    algebraMap (ZMod p) Ω (f (Sum.inl (V.rep 0 0)) α) -
      ∑ i : V.AuxIdx, (algebraMap (ZMod p) Ω (f (Sum.inr i) (α - algebraMap K Ω (ε.E i.1))) -
        algebraMap (ZMod p) Ω (f (Sum.inr i) α)) -
      Finsupp.single (algebraMap K Ω (V.instanceEnc ε x)) (1 : Ω) α = 0 := by sorry
