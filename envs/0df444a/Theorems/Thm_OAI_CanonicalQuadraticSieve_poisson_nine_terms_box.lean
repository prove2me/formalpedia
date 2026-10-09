-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_poisson_nine_terms_box
-- name    : OAI.CanonicalQuadraticSieve.poisson_nine_terms_box
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T00:19:38.731439+00:00
-- url     : https://prove2.me/theorems/2c32d0ae-f9f0-4ea5-bcca-efb5f217378b
-- title:
--   Bookkeeping bound for the nine Poisson error terms
-- statement:
--   Let $U\ge1$ and $S\ge0$, and let fifteen reals $d,l_k,l_n,f,e,v_h,v_z,d_v,u_h,d_u,\mathrm{lat},c_d,c_s,c_t,c_p$ all lie in $[0,U]$. Let $M,N,a\ge0$ and $T\ge1$ with $M\le S$, $N\le S$, $Ta\le S$, and let $b,e_D,e_S,\mathrm{tail}$ lie in $[0,S]$. Then
--   $$d\,l_k\big(8v_hl_n^2fe(M+a)+8v_zl_n^2fe(M+2Ta)+8l_n^2\,\mathrm{lat}\,d_vfe(M+2Ta)+65536\,c_de_D\big)+1536\,d\,c_t\,\mathrm{tail}+l_k\big(2u_hdl_n^2fe(4N/T+a)+2dl_n^2\,\mathrm{lat}\,d_ufe(N+2Ta)+32768\,c_se_S\big)+u_hd^2c_pb\le262144\,U^8S.$$
--
--   Lean: `OAI.CanonicalQuadraticSieve.poisson_nine_terms_box` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open Filter
open Filter
open scoped Topology
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open UniqueFactorizationMonoid
open scoped BigOperators

namespace CanonicalQuadraticSieve

theorem poisson_nine_terms_box
    (d lk ln f e vh vz dv uh du lat cd cs ct cp M N T a b eD eS tail U S : ℝ)
    (hU : 1≤U) (hS : 0≤S)
    (hbudget : ∀x∈([d,lk,ln,f,e,vh,vz,dv,uh,du,lat,cd,cs,ct,cp] : List ℝ), 0≤x ∧ x≤U)
    (hM : 0≤M) (hN : 0≤N) (hT : 1≤T) (ha : 0≤a)
    (hMS : M≤S) (hNS : N≤S) (hTa : T*a≤S)
    (hb : 0≤b ∧ b≤S) (hED : 0≤eD ∧ eD≤S) (hES : 0≤eS ∧ eS≤S)
    (htail : 0≤tail ∧ tail≤S) :
    d*lk*(8*vh*ln^2*f*e*(M+a) + 8*vz*ln^2*f*e*(M+2*T*a) +
      8*ln^2*lat*dv*f*e*(M+2*T*a) + 65536*cd*eD) +
    1536*d*ct*tail +
    lk*(2*uh*d*ln^2*f*e*(4*N/T+a) + 2*d*ln^2*lat*du*f*e*(N+2*T*a) +
      32768*cs*eS) + uh*d^2*cp*b ≤ 262144*U^8*S := by
  sorry

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

end

end OAI
end
