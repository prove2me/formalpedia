-- Prove2me | Theorems.Thm_HodgeComputer_Formal_HoldoutCover_finiteNormalizedTrace_firstOrder
-- name    : HodgeComputer.Formal.HoldoutCover.finiteNormalizedTrace_firstOrder
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:23:13.373533+00:00
-- url     : https://prove2.me/theorems/98cb0d31-a00a-4140-b6ea-d040774627fa
-- title:
--   Descent of first-order linear PDEs via normalized field trace
-- statement:
--   Let $L / K$ be a finite field extension with $\operatorname{char}(K) = 0$, let $\iota$ be a finite type, and let $D_i \in \operatorname{Der}_{\mathbb{Z}}(K, K)$ and $E_i \in \operatorname{Der}_{\mathbb{Z}}(L, L)$ be compatible derivations satisfying $E_i(\iota_{K \to L}(x)) = \iota_{K \to L}(D_i(x))$ for all $i, x$. Suppose $c : \iota \to K$, $f \in K$, and $u : \iota \to L$ solve the first-order equation
--
--   $$\sum_{i \in \iota} \bigl(E_i(u_i) + u_i \cdot \iota_{K \to L}(c_i)\bigr) = \iota_{K \to L}(f).$$
--
--   Then the descended vector $v_i = \operatorname{Tr}^{\mathrm{norm}}_{L/K}(u_i) \in K$ solves
--
--   $$\sum_{i \in \iota} \bigl(D_i(v_i) + v_i c_i\bigr) = f.$$
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/HoldoutCover/FiniteTrace.lean#L1-L221

import Mathlib.FieldTheory.NormalizedTrace
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Trace.Basic
set_option autoImplicit false
open scoped BigOperators

theorem HodgeComputer.Formal.HoldoutCover.finiteNormalizedTrace_firstOrder
    {K L ι : Type*} [Field K] [CharZero K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Fintype ι]
    (D : ι → Derivation ℤ K K) (E : ι → Derivation ℤ L L)
    (compatible : ∀ i x, E i (algebraMap K L x) = algebraMap K L (D i x))
    (c : ι → K) (f : K) (u : ι → L)
    (h : ∑ i, (E i (u i) + u i * algebraMap K L (c i)) = algebraMap K L f) :
    ∑ i, (D i (Algebra.normalizedTrace K L (u i)) +
      Algebra.normalizedTrace K L (u i) * c i) = f := by sorry
