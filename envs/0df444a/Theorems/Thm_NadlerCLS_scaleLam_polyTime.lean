-- Prove2me | Theorems.Thm_NadlerCLS_scaleLam_polyTime
-- name    : NadlerCLS.scaleLam_polyTime
-- status  : Proved
-- author  : @utkuokur
-- created : 2026-11-12T19:54:01.63601+00:00
-- url     : https://prove2.me/theorems/6a58581a-f985-461d-b1d1-8a30cbd0237b
-- title:
--   The instance map $(f,p,\delta,\lambda)\mapsto(f,p,\delta,\lambda')$ with $\lambda'\ge n\lambda$ of Theorem C.3 is polynomial-time
-- statement:
--   Fix a dimension $n$. An instance of Continuous-LocalOpt, or of $\beta$-Hölder-LocalOpt, on $[0,1]^n$ is a tuple $I=(f,p,\delta,\lambda)$ of two arithmetic circuits and two positive rational parameters, given by its binary code $\operatorname{enc}(I)$.
--
--   The lemma states that the instance construction in the proof of Theorem C.3 can be carried out in polynomial time on codes: there is a map $F$ on binary strings, computable in polynomial time by a deterministic one-tape Turing machine, such that for every valid instance $(f,p,\delta,\lambda)$ there is a rational number $\lambda'$ with
--
--   $$
--   \lambda'\;\ge\; n\lambda
--   \qquad\text{and}\qquad
--   F\bigl(\operatorname{enc}(f,p,\delta,\lambda)\bigr)\;=\;\operatorname{enc}(f,p,\delta,\lambda').
--   $$
--
--   The circuits $f$ and $p$ and the parameter $\delta$ are left unchanged; only the last parameter is enlarged.
--
--   This is the instance-map half of the reduction from Continuous-LocalOpt to $\beta$-Hölder-LocalOpt. With $t=\lVert x-y\rVert_1\le n$, a violation $\lVert f(x)-f(y)\rVert_1>\lambda' t^{\beta}$ of the Hölder bound of the constructed instance is a violation $\lVert f(x)-f(y)\rVert_1>\lambda t$ of the Lipschitz bound of the original instance.
--
--   Differences from the source:
--   - weakening: the paper's target instance is $(f,p,\delta,n\lambda)$ (p.37) → any $\lambda'\ge n\lambda$ is allowed, and $\lambda'$ may depend on the instance; reason: the proof of Theorem C.3 only uses $\lambda'\ge n\lambda$, and the paper's choice $\lambda'=n\lambda$ satisfies the statement
--   - generalization: the statement is made for every $n\ge 0$; for $n\le 1$ the identity map already satisfies it
--   - encoding: $F$ is a function on all binary strings and is constrained only on codes of valid instances
--
--   **Formalization Note** `PolyTime` is the public alias of `CookPvsNP.PolyTimeComputable`. An instance is valid (`COInstance.Valid`) if both circuits are well-behaved with the right numbers of inputs and outputs and $\delta>0$, $\lambda>0$. The code is `encCO`.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101v4 (3 Nov 2026), https://arxiv.org/abs/2609.14101, proof of Theorem C.3, p.37 ("We construct the β-HÖLDER-LOCALOPT instance I_HO := (f, p, δ, nλ). This construction clearly has polynomial size"); Section 2, p.7 (polynomial-time many-one reductions).

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NadlerCLS_COInstance

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- **The instance map of Theorem C.3 is polynomial-time** (Xiong–Vlatakis-Gkaragkounis, *On the
Complexity of Finding Fixed Points for Set-Valued Contractions*, arXiv:2609.14101v4, proof of
Theorem C.3, p.37: "We construct the β-HÖLDER-LOCALOPT instance I_HO := (f, p, δ, nλ). This
construction clearly has polynomial size"). Some polynomial-time computable map on binary strings
sends the code of every valid instance `(f, p, δ, λ)` on `[0, 1]ⁿ` to the code of an instance
`(f, p, δ, λ')` with the same circuits, the same `δ`, and `λ' ≥ n λ`.

**Formalization Note** The paper takes `λ' = n λ`; the proof of Theorem C.3 only uses
`λ' ≥ n λ`, so any such `λ'` (which may depend on the instance) is allowed. The map is constrained
only on codes of valid instances. -/
theorem scaleLam_polyTime (n : ℕ) :
    ∃ F : List Bool → List Bool, PolyTime F ∧
      ∀ I : COInstance n, I.Valid →
        ∃ lam' : ℚ, (n : ℚ) * I.lam ≤ lam' ∧
          F (encCO I) =
            encCO ({ f := I.f, p := I.p, δ := I.δ, lam := lam' } : COInstance n) := by sorry

end NadlerCLS
