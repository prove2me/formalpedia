-- Prove2me | Theorems.Thm_Kyprianou_Ch01_chapterOneCertificatesStable2SourceExact
-- name    : Kyprianou.Ch01.chapterOneCertificatesStable2SourceExact
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T20:13:57.705149+00:00
-- url     : https://prove2.me/theorems/f61e3611-af10-4f59-8458-32fa5d158a9f
-- title:
--   Source-exact Chapter 1 stable exponent pair certificate
-- statement:
--   Exactly the original two Chapter 1 stable-exponent source certificates at positions 49 and 50 of the cumulative 67-way theorem, for non-index-one and index-one stable processes. Both keep the original mathematical hypotheses and exponent conventions. The dependency proof uses mathematically source-identical versioned global theorem declarations that import the targeted Lévy exponent Definition, because remote compiler probes showed each legacy exponent theorem module collides with the current published certificate Definition even when imported individually.
-- source:
--   Kyprianou (2006), Chapter 1 stable-process characteristic exponent cases §1.2.6, all-67 certificate Definition; original theorem UUIDs 14129268-8e81-434d-ac80-084d68b6b631 and 802ca6d6-48be-4ce7-bad9-dffd367b9cff.

import Definitions.Def_Kyprianou_Ch01_All67CertificatesTargetedV3
set_option maxRecDepth 4000
open Kyprianou.Ch01
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch01.chapterOneCertificatesStable2SourceExact :
    certificate_stableLevyExponentFormAwayFromOne ∧
    certificate_stableLevyExponentFormIndexOne := by
  sorry
