-- Prove2me | Theorems.Thm_LiouvilleDiffAlg_ratFunc_descent_log
-- name    : LiouvilleDiffAlg.ratFunc_descent_log
-- status  : Open
-- author  : @vebis
-- created : 2026-10-01T11:41:24.205925+00:00
-- url     : https://prove2.me/theorems/70e30465-10ac-4f72-8e35-216269c8fb23
-- title:
--   Liouville descent for a logarithmic generator over K(X)
-- statement:
--   Throughout, $K$ is a field of characteristic zero with a derivation $D$, and $K(X)$ is the field of rational functions in one variable over $K$, equipped with a derivation (also written $D$) that extends the derivation of $K$. Suppose $X$ is a logarithmic generator over $K$: $DX = Ds/s$ for some nonzero $s\in K$, and suppose every element of $K(X)$ with zero derivative lies in $K$. Let $h\in K$, let $c_1,\dots,c_n\in K$ be constants, let $u_1,\dots,u_n\in K(X)$ be nonzero and $v\in K(X)$ with
--
--   $$h=\sum_{i=1}^n c_i\frac{Du_i}{u_i}+Dv.$$
--
--   Then there exist $m\ge0$, constants $c'_1,\dots,c'_m\in K$, nonzero $a_1,\dots,a_m\in K$ and $b\in K$ with
--
--   $$h=\sum_{j=1}^m c'_j\frac{Da_j}{a_j}+Db.$$
--
--   This is the logarithmic case of the descent step in the proof of Liouville's theorem on elementary antiderivatives.
--
--   **Formalization Note** The field $K(X)$ is `RatFunc K`; the hypothesis on constants is stated as `hcon`.
-- source:
--   Rosenlicht, Integration in finite terms, Amer. Math. Monthly 79 (1972), 963–972 (proof of Liouville's theorem by induction on an elementary tower); Geddes–Czapor–Labahn, Algorithms for Computer Algebra (Kluwer, 1992), §12.4; Wikipedia, "Liouville's theorem (differential algebra)", oldid=1349223559, section "Basic theorem"

import Mathlib

open scoped Differential
open Polynomial

namespace LiouvilleDiffAlg

theorem ratFunc_descent_log {K : Type*} [Field K] [Differential K] [CharZero K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    {s : K} (hs : s ≠ 0) (hX : (RatFunc.X : RatFunc K)′ = algebraMap K (RatFunc K) (s′ / s))
    (hcon : ∀ x : RatFunc K, x′ = 0 → x ∈ Set.range (algebraMap K (RatFunc K)))
    {n : ℕ} (c : Fin n → K) (hc : ∀ i, (c i)′ = 0) (h : K)
    (u : Fin n → RatFunc K) (hu : ∀ i, u i ≠ 0) (v : RatFunc K)
    (hfe : algebraMap K (RatFunc K) h = ∑ i, algebraMap K (RatFunc K) (c i) * ((u i)′ / u i) + v′) :
    ∃ (m : ℕ) (c' a : Fin m → K) (b : K), (∀ i, (c' i)′ = 0) ∧ (∀ i, a i ≠ 0) ∧
      h = ∑ i, c' i * ((a i)′ / a i) + b′ := by sorry

end LiouvilleDiffAlg
